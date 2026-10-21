-- Prove2me | solution 1 for VolunteerEngage.Thresholds.eq_E9
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:03:03.841305+00:00
-- url     : https://prove2.me/submissions/5a107733-d82e-45ea-b812-8ac6a61aa5a1

import Mathlib
import Definitions.Def_VolunteerEngage_Thresholds_Setting

set_option autoImplicit false
open VolunteerEngage.Thresholds

lemma vet_theta_succ (M : Model) (l : ℕ) : M.θ (l + 1) = M.θ l + M.η (l + 1) := by
  simp [Model.θ, Finset.sum_Icc_succ_top]
  ring

lemma vet_theta_step (M : Model) (hM : M.Standing) (l : ℕ) (hl : l + 1 ≤ M.L) :
    M.θ l ≤ M.θ (l + 1) := by
  rw [vet_theta_succ]
  have := hM.2.2.1 (l + 1) (Finset.mem_Icc.mpr ⟨by omega, hl⟩)
  linarith

lemma vet_theta_mono (M : Model) (hM : M.Standing) (k l : ℕ) (hkl : k ≤ l) (hl : l ≤ M.L) :
    M.θ k ≤ M.θ l := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih => exact (ih (by omega)).trans (vet_theta_step M hM n hl)

lemma vet_c_mono (M : Model) (hM : M.Standing) (k l : ℕ) (hk : 1 ≤ k) (hkl : k ≤ l)
    (hl : l ≤ M.L) : M.c k ≤ M.c l := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih =>
    have := hM.2.2.2.2.1 n (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    exact (ih (by omega)).trans this.le

/-- one summand of the cost -/
noncomputable def vetA (M : Model) (l : ℕ) (x : ℝ) : ℝ :=
  min (M.θ l) (max (M.θ (l - 1)) x) - M.θ (l - 1)

lemma vet_tele (M : Model) (hM : M.Standing) (x : ℝ) :
    ∀ n, n ≤ M.L → ∑ l ∈ Finset.Icc 1 n, vetA M l x = min (M.θ n) (max (M.θ 0) x) - M.θ 0 := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]
    unfold vetA
    have h1 := vet_theta_step M hM n hn
    have h2 := vet_theta_mono M hM 0 n (by omega) (by omega)
    simp only [Nat.add_sub_cancel]
    simp only [min_def, max_def]
    split_ifs <;> linarith

lemma vet_cost_eq (M : Model) (x : ℝ) :
    cost M x = ∑ l ∈ Finset.Icc 1 M.L, M.c l * vetA M l x := rfl

lemma vet_g_eq (M : Model) (hM : M.Standing) (y x : ℝ) (hx : x ∈ Set.Icc M.θ0 (M.θ M.L)) :
    y * x - cost M x = y * M.θ0 + ∑ l ∈ Finset.Icc 1 M.L, (y - M.c l) * vetA M l x := by
  have ht := vet_tele M hM x M.L le_rfl
  have h0 : M.θ 0 = M.θ0 := by simp [Model.θ]
  rw [h0] at ht
  have hm : min (M.θ M.L) (max M.θ0 x) = x := by
    rw [max_eq_right hx.1, min_eq_right hx.2]
  rw [hm] at ht
  have : ∑ l ∈ Finset.Icc 1 M.L, (y - M.c l) * vetA M l x
      = y * (x - M.θ0) - cost M x := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ht, vet_cost_eq]
  rw [this]; ring

lemma vet_E9_core (M : Model) (hM : M.Standing) (y : ℝ) (k : ℕ) (hk : k ≤ M.L)
    (h1 : ∀ l ∈ Finset.Icc 1 M.L, l ≤ k → M.c l ≤ y)
    (h2 : ∀ l ∈ Finset.Icc 1 M.L, k < l → y ≤ M.c l) :
    phi M y = y * M.θ k - cost M (M.θ k) := by
  have h0 : M.θ 0 = M.θ0 := by simp [Model.θ]
  have hkm : M.θ k ∈ Set.Icc M.θ0 (M.θ M.L) :=
    ⟨h0 ▸ vet_theta_mono M hM 0 k (by omega) hk, vet_theta_mono M hM k M.L hk le_rfl⟩
  unfold phi
  apply IsGreatest.csSup_eq
  refine ⟨⟨M.θ k, hkm, rfl⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  simp only
  rw [vet_g_eq M hM y x hx, vet_g_eq M hM y _ hkm]
  apply add_le_add_right (Finset.sum_le_sum ?_)
  intro l hl
  obtain ⟨hl1, hlL⟩ := Finset.mem_Icc.mp hl
  obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
  have hjθ := vet_theta_step M hM j hlL
  unfold vetA
  simp only [Nat.add_sub_cancel]
  rcases le_or_gt (j + 1) k with hlk | hlk
  · have hy := h1 (j + 1) hl hlk
    have hθk : M.θ (j + 1) ≤ M.θ k := vet_theta_mono M hM _ _ hlk hk
    have : min (M.θ (j + 1)) (max (M.θ j) (M.θ k)) = M.θ (j + 1) := by
      rw [max_eq_right (hjθ.trans hθk), min_eq_left hθk]
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    have : min (M.θ (j + 1)) (max (M.θ j) x) ≤ M.θ (j + 1) := min_le_left _ _
    linarith
  · have hy := h2 (j + 1) hl hlk
    have hθk : M.θ k ≤ M.θ j := vet_theta_mono M hM _ _ (by omega) (by omega)
    have : min (M.θ (j + 1)) (max (M.θ j) (M.θ k)) = M.θ j := by
      rw [max_eq_left hθk, min_eq_right hjθ]
    rw [this]
    have hnn : 0 ≤ min (M.θ (j + 1)) (max (M.θ j) x) - M.θ j := by
      have : M.θ j ≤ min (M.θ (j + 1)) (max (M.θ j) x) :=
        le_min hjθ (le_max_left _ _)
      linarith
    have : (y - M.c (j + 1)) * (min (M.θ (j + 1)) (max (M.θ j) x) - M.θ j) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hnn
    simp only [sub_self, mul_zero]
    exact this

lemma vet_cost_theta0 (M : Model) (hM : M.Standing) : cost M (M.θ 0) = 0 := by
  unfold cost
  apply Finset.sum_eq_zero
  intro l hl
  obtain ⟨hl1, hlL⟩ := Finset.mem_Icc.mp hl
  obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
  have h1 := vet_theta_step M hM j hlL
  have h2 := vet_theta_mono M hM 0 j (by omega) (by omega)
  simp only [Nat.add_sub_cancel]
  rw [max_eq_left h2, min_eq_right h1]
  simp

theorem solution (M : Model) (hM : M.Standing) :
    (∀ y : ℝ, y ≤ M.c 1 → phi M y = M.θ 0 * y) ∧
    (∀ m ∈ Finset.Icc 2 M.L, ∀ y : ℝ, M.c (m - 1) < y → y ≤ M.c m →
      phi M y = M.θ (m - 1) * y - cost M (M.θ (m - 1))) ∧
    (∀ y : ℝ, M.c M.L < y → phi M y = M.θ M.L * y - cost M (M.θ M.L)) := by
  have hL : 1 ≤ M.L := hM.1
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    have := vet_E9_core M hM y 0 (by omega)
      (fun l hl h => by have := (Finset.mem_Icc.mp hl).1; omega)
      (fun l hl _ => hy.trans (vet_c_mono M hM 1 l le_rfl (Finset.mem_Icc.mp hl).1 (Finset.mem_Icc.mp hl).2))
    rw [this, vet_cost_theta0 M hM]; ring
  · intro m hm y hy1 hy2
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    have := vet_E9_core M hM y (m - 1) (by omega)
      (fun l hl h => (vet_c_mono M hM l (m - 1) (Finset.mem_Icc.mp hl).1 h (by omega)).trans hy1.le)
      (fun l hl h => hy2.trans (vet_c_mono M hM m l (by omega) (by omega) (Finset.mem_Icc.mp hl).2))
    rw [this]; ring
  · intro y hy
    have := vet_E9_core M hM y M.L le_rfl
      (fun l hl h => (vet_c_mono M hM l M.L (Finset.mem_Icc.mp hl).1 (Finset.mem_Icc.mp hl).2 le_rfl).trans hy.le)
      (fun l hl h => by have := (Finset.mem_Icc.mp hl).2; omega)
    rw [this]; ring
