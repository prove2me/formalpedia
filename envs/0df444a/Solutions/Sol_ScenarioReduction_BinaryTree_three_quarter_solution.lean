-- Prove2me | solution 1 for ScenarioReduction.BinaryTree.three_quarter_solution
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T19:30:50.601482+00:00
-- url     : https://prove2.me/submissions/c44d4c5c-76f1-4dd8-bad7-9779a995efef

import Mathlib
import Definitions.Def_ScenarioReduction_BinaryTree_scenario
import Definitions.Def_ScenarioReduction_BinaryTree_IStar
import Definitions.Def_ScenarioReduction_BinaryTree_redCost



namespace ScenarioReduction.BinaryTree

open Finset

variable {K : ℕ}

lemma scen_sub (δ : ℕ → ℝ) (σ τ : Fin K → Fin 2) (k : Fin (K + 1)) :
    (scenario δ σ - scenario δ τ) k =
      ∑ r ∈ Icc 1 k.val, 2 * (((lev σ r).val : ℝ) - (lev τ r).val) * δ r := by
  simp only [Pi.sub_apply, scenario, ← sum_sub_distrib]
  apply sum_congr rfl; intro r _; ring

lemma fin2_abs {a b : Fin 2} (h : a ≠ b) : |((a.val : ℝ) - b.val)| = 1 := by
  fin_cases a <;> fin_cases b <;> simp_all

lemma coord_first_diff (δ : ℕ → ℝ) (σ τ : Fin K → Fin 2) (l : ℕ) (hl : l ∈ Icc 1 K)
    (hdiff : lev σ l ≠ lev τ l) (hagree : ∀ r ∈ Icc 1 (l - 1), lev σ r = lev τ r)
    (hδ : 0 ≤ δ l) :
    |(scenario δ σ - scenario δ τ) ⟨l, by rw [mem_Icc] at hl; omega⟩| = 2 * δ l := by
  rw [scen_sub]
  rw [sum_eq_single_of_mem l (by rw [mem_Icc] at hl ⊢; simp; omega)]
  · rw [abs_mul, abs_mul, fin2_abs hdiff, abs_of_nonneg hδ]; norm_num
  · intro r hr hrl
    simp only [mem_Icc] at hr
    rw [hagree r (by rw [mem_Icc]; omega)]; ring

theorem distance_bound (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (σ τ : Fin K → Fin 2) (l : ℕ) (hl : l ∈ Finset.Icc 1 K) (hdiff : lev σ l ≠ lev τ l)
    (hagree : ∀ r ∈ Finset.Icc 1 (l - 1), lev σ r = lev τ r) :
    2 * δ l ≤ ‖scenario δ σ - scenario δ τ‖ ∧ 2 * δ k0 ≤ ‖scenario δ σ - scenario δ τ‖ := by
  have h1 := coord_first_diff δ σ τ l hl hdiff hagree (hδ l hl)
  have h2 := norm_le_pi_norm (scenario δ σ - scenario δ τ) ⟨l, by rw [mem_Icc] at hl; omega⟩
  rw [Real.norm_eq_abs, h1] at h2
  exact ⟨h2, by linarith [hmin l hl]⟩

lemma exists_first_diff (σ τ : Fin K → Fin 2) (h : σ ≠ τ) :
    ∃ l ∈ Icc 1 K, lev σ l ≠ lev τ l ∧ ∀ r ∈ Icc 1 (l - 1), lev σ r = lev τ r := by
  have hex : ∃ m, ∃ hm : m < K, σ ⟨m, hm⟩ ≠ τ ⟨m, hm⟩ := by
    by_contra hc; push_neg at hc; exact h (funext fun i => hc i.val i.isLt)
  classical
  let m := Nat.find hex
  obtain ⟨hm, hne⟩ := Nat.find_spec hex
  refine ⟨m + 1, by rw [mem_Icc]; omega, ?_, ?_⟩
  · unfold lev; rw [dif_pos (by omega), dif_pos (by omega)]; simpa using hne
  · intro r hr
    rw [mem_Icc] at hr
    unfold lev; rw [dif_pos (by omega), dif_pos (by omega)]
    have := Nat.find_min hex (show r - 1 < m by omega)
    push_neg at this; exact this (by omega)

lemma sep (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (σ τ : Fin K → Fin 2) (h : σ ≠ τ) : 2 * δ k0 ≤ ‖scenario δ σ - scenario δ τ‖ := by
  obtain ⟨l, hl, hd, ha⟩ := exists_first_diff σ τ h
  exact (distance_bound K δ hδ k0 hk0 hmin σ τ l hl hd ha).2

theorem redCost_lower_bound (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (n : ℕ) (hn : n < 2 ^ K) (J : Finset (Fin K → Fin 2)) (hJcard : J.card = 2 ^ K - n)
    (hJ : Jᶜ.Nonempty) :
    ((2 : ℝ) ^ K - n) / 2 ^ K * (2 * δ k0) ≤ redCost δ J hJ := by
  unfold redCost
  have hterm : ∀ σ ∈ J, (1 / (2 ^ K : ℝ)) * (2 * δ k0) ≤
      (1 / (2 ^ K : ℝ)) * Jᶜ.inf' hJ (fun τ => ‖scenario δ σ - scenario δ τ‖) := by
    intro σ hσ
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply le_inf'; intro τ hτ
    apply sep K δ hδ k0 hk0 hmin
    rintro rfl; rw [mem_compl] at hτ; exact hτ hσ
  refine le_trans ?_ (sum_le_sum hterm)
  rw [sum_const, hJcard, nsmul_eq_mul, Nat.cast_sub hn.le]; push_cast
  apply le_of_eq; ring


def flipAt (σ : Fin K → Fin 2) (m : ℕ) : Fin K → Fin 2 :=
  fun i => if i.val + 1 = m then 1 - σ i else σ i

lemma lev_flip (σ : Fin K → Fin 2) {m : ℕ} (hm1 : 1 ≤ m) (hmK : m ≤ K) (r : ℕ) :
    lev (flipAt σ m) r = if r = m then 1 - lev σ r else lev σ r := by
  unfold lev flipAt
  by_cases hr : 1 ≤ r ∧ r ≤ K
  · rw [dif_pos hr, dif_pos hr]
    by_cases h : r = m
    · rw [if_pos (by simp; omega), if_pos h]
    · rw [if_neg (by simp; omega), if_neg h]
  · rw [dif_neg hr, dif_neg hr, if_neg (by omega)]

def eps (a : Fin 2) : ℝ := ((1 - a : Fin 2).val : ℝ) - (a.val : ℝ)

lemma eps_abs (a : Fin 2) : |eps a| = 1 := by fin_cases a <;> simp [eps] <;> norm_num

lemma eps_neg {a b : Fin 2} (h : a ≠ b) : eps b = -eps a := by
  fin_cases a <;> fin_cases b <;> simp_all [eps] <;> norm_num

lemma two_coord (δ : ℕ → ℝ) (i j : Fin K → Fin 2) (m1 m2 : ℕ) (hne : m1 ≠ m2)
    (hag : ∀ r, r ≠ m1 → r ≠ m2 → lev i r = lev j r) (k : Fin (K + 1)) :
    (scenario δ i - scenario δ j) k =
      (if m1 ∈ Icc 1 k.val then 2 * (((lev i m1).val : ℝ) - (lev j m1).val) * δ m1 else 0) +
      (if m2 ∈ Icc 1 k.val then 2 * (((lev i m2).val : ℝ) - (lev j m2).val) * δ m2 else 0) := by
  rw [scen_sub]
  have : ∀ r ∈ Icc 1 k.val, 2 * (((lev i r).val : ℝ) - (lev j r).val) * δ r =
      (if r = m1 then 2 * (((lev i m1).val : ℝ) - (lev j m1).val) * δ m1 else 0) +
      (if r = m2 then 2 * (((lev i m2).val : ℝ) - (lev j m2).val) * δ m2 else 0) := by
    intro r _
    by_cases h1 : r = m1
    · subst h1; rw [if_pos rfl, if_neg hne]; ring
    · by_cases h2 : r = m2
      · subst h2; rw [if_neg h1, if_pos rfl]; ring
      · rw [if_neg h1, if_neg h2, hag r h1 h2]; ring
  rw [sum_congr rfl this, sum_add_distrib, sum_ite_eq', sum_ite_eq']

lemma norm_eq_of_coords (v : Fin (K + 1) → ℝ) (k0 m : ℕ) (hk0 : 1 ≤ k0) (hk0K : k0 ≤ K)
    (hm : k0 < m) (x1 x2 d0 dm : ℝ)
    (hv : ∀ k : Fin (K + 1), v k = (if k0 ∈ Icc 1 k.val then 2 * x1 * d0 else 0) +
      (if m ∈ Icc 1 k.val then 2 * x2 * dm else 0))
    (hx1 : |x1| = 1) (hx2 : x2 = 0 ∨ x2 = -x1) (h0 : 0 ≤ d0) (h1 : d0 ≤ dm) (h2 : dm ≤ 2 * d0) :
    ‖v‖ = 2 * d0 := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (by linarith)]
    intro k
    rw [hv k, Real.norm_eq_abs]
    split_ifs with ha hb hb
    · rcases hx2 with rfl | rfl
      · rw [show 2 * x1 * d0 + 2 * 0 * dm = 2 * x1 * d0 by ring, abs_mul, abs_mul, hx1]
        simp [abs_of_nonneg h0]
      · have : 2 * x1 * d0 + 2 * -x1 * dm = 2 * x1 * (d0 - dm) := by ring
        rw [this, abs_mul, abs_mul, hx1, abs_of_nonpos (show d0 - dm ≤ 0 by linarith)]
        norm_num; linarith
    · rw [add_zero, abs_mul, abs_mul, hx1]; simp [abs_of_nonneg h0]
    · exfalso; rw [mem_Icc] at ha hb; omega
    · simp; linarith
  · have h := norm_le_pi_norm v ⟨k0, by omega⟩
    rw [hv, if_pos (by rw [mem_Icc]; simp; omega), if_neg (by rw [mem_Icc]; simp; omega),
      add_zero, Real.norm_eq_abs, abs_mul, abs_mul, hx1] at h
    simpa [abs_of_nonneg h0] using h

lemma lev_flip1 (σ : Fin K → Fin 2) {m : ℕ} (hm1 : 1 ≤ m) (hmK : m ≤ K) (r : ℕ) :
    lev (flipAt σ m) r = if r = m then 1 - lev σ r else lev σ r := lev_flip σ hm1 hmK r

lemma lev_flip2 (σ : Fin K → Fin 2) {m1 m2 : ℕ} (h1 : 1 ≤ m1) (h1K : m1 ≤ K) (h2 : 1 ≤ m2)
    (h2K : m2 ≤ K) (hne : m1 ≠ m2) (r : ℕ) :
    lev (flipAt (flipAt σ m1) m2) r = if r = m1 ∨ r = m2 then 1 - lev σ r else lev σ r := by
  rw [lev_flip _ h2 h2K, lev_flip σ h1 h1K]
  by_cases a : r = m1
  · have b : ¬ r = m2 := by omega
    rw [if_neg b, if_pos a, if_pos (Or.inl a)]
  · by_cases b : r = m2
    · rw [if_pos b, if_neg a, if_pos (Or.inr b)]
    · rw [if_neg b, if_neg a, if_neg (by tauto)]

lemma caseA : ∀ a b c : Fin 2, (a ≠ b → b ≠ c) → b = c → (1 - a ≠ b ∧ b = c) := by decide
lemma caseB : ∀ a b c : Fin 2, b ≠ c → a = b → (1 - a ≠ b ∧ b = 1 - c) := by decide
lemma caseC : ∀ a b c : Fin 2, b ≠ c → a ≠ b → (1 - a ≠ 1 - b ∧ 1 - b = c) := by decide

theorem partner_exists (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (hK : 3 ≤ K) (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K)
    (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k) (hk0K : k0 ≤ K - 2)
    (hmax : max (δ (k0 + 1)) (δ (k0 + 2)) ≤ 2 * δ k0) :
    ∀ j ∉ IStar K k0, ∃ i ∈ IStar K k0, ‖scenario δ i - scenario δ j‖ = 2 * δ k0 := by
  intro j hj
  rw [mem_Icc] at hk0
  have hd0 := hδ k0 (by rw [mem_Icc]; omega)
  have hd1 := hmin (k0 + 1) (by rw [mem_Icc]; omega)
  have hd2 := hmin (k0 + 2) (by rw [mem_Icc]; omega)
  have hm1 := (le_max_left _ _).trans hmax
  have hm2 := (le_max_right _ _).trans hmax
  simp only [IStar, mem_filter, mem_univ, true_and, not_and] at hj ⊢
  by_cases hbc : lev j (k0 + 1) = lev j (k0 + 2)
  · refine ⟨flipAt j k0, ?_, ?_⟩
    · rw [lev_flip1 j hk0.1 hk0.2, lev_flip1 j hk0.1 hk0.2, lev_flip1 j hk0.1 hk0.2]
      simp only [if_true, show k0 + 1 ≠ k0 by omega, show k0 + 2 ≠ k0 by omega, if_false]
      exact caseA _ _ _ hj hbc
    · apply norm_eq_of_coords _ k0 (k0 + 1) hk0.1 hk0.2 (by omega) (eps (lev j k0)) 0
        (δ k0) (δ (k0 + 1)) _ (eps_abs _) (Or.inl rfl) hd0 hd1 hm1
      intro k
      rw [two_coord δ (flipAt j k0) j k0 (k0 + 1) (by omega) (fun r h1 _ => by
        rw [lev_flip1 j hk0.1 hk0.2, if_neg h1]) k]
      have e0 : lev (flipAt j k0) k0 = 1 - lev j k0 := by
        rw [lev_flip1 j hk0.1 hk0.2, if_pos rfl]
      have e1 : lev (flipAt j k0) (k0 + 1) = lev j (k0 + 1) := by
        rw [lev_flip1 j hk0.1 hk0.2, if_neg (by omega)]
      rw [e0, e1]; simp only [eps, sub_self, mul_zero, zero_mul]
  · by_cases hab : lev j k0 = lev j (k0 + 1)
    · refine ⟨flipAt (flipAt j k0) (k0 + 2), ?_, ?_⟩
      · rw [lev_flip2 j hk0.1 hk0.2 (by omega) (by omega) (by omega),
          lev_flip2 j hk0.1 hk0.2 (by omega) (by omega) (by omega),
          lev_flip2 j hk0.1 hk0.2 (by omega) (by omega) (by omega)]
        simp only [true_or, or_true, if_true, show k0 + 1 ≠ k0 by omega,
          show k0 + 1 ≠ k0 + 2 by omega, or_self, if_false]
        exact caseB _ _ _ hbc hab
      · have hac : lev j k0 ≠ lev j (k0 + 2) := by rw [hab]; exact hbc
        apply norm_eq_of_coords _ k0 (k0 + 2) hk0.1 hk0.2 (by omega) (eps (lev j k0))
          (eps (lev j (k0 + 2))) (δ k0) (δ (k0 + 2)) _ (eps_abs _) (Or.inr (eps_neg hac))
          hd0 hd2 hm2
        intro k
        rw [two_coord δ _ j k0 (k0 + 2) (by omega) (fun r h1 h2 => by
          rw [lev_flip2 j hk0.1 hk0.2 (by omega) (by omega) (by omega), if_neg (by tauto)]) k]
        have e0 : lev (flipAt (flipAt j k0) (k0 + 2)) k0 = 1 - lev j k0 := by
          rw [lev_flip2 j hk0.1 hk0.2 (by omega) (by omega) (by omega), if_pos (Or.inl rfl)]
        have e2 : lev (flipAt (flipAt j k0) (k0 + 2)) (k0 + 2) = 1 - lev j (k0 + 2) := by
          rw [lev_flip2 j hk0.1 hk0.2 (by omega) (by omega) (by omega), if_pos (Or.inr rfl)]
        rw [e0, e2]; simp only [eps]
    · refine ⟨flipAt (flipAt j k0) (k0 + 1), ?_, ?_⟩
      · rw [lev_flip2 j hk0.1 hk0.2 (by omega) (by omega) (by omega),
          lev_flip2 j hk0.1 hk0.2 (by omega) (by omega) (by omega),
          lev_flip2 j hk0.1 hk0.2 (by omega) (by omega) (by omega)]
        simp only [true_or, or_true, if_true, show k0 + 2 ≠ k0 by omega,
          show k0 + 2 ≠ k0 + 1 by omega, or_self, if_false]
        exact caseC _ _ _ hbc hab
      · apply norm_eq_of_coords _ k0 (k0 + 1) hk0.1 hk0.2 (by omega) (eps (lev j k0))
          (eps (lev j (k0 + 1))) (δ k0) (δ (k0 + 1)) _ (eps_abs _) (Or.inr (eps_neg hab))
          hd0 hd1 hm1
        intro k
        rw [two_coord δ _ j k0 (k0 + 1) (by omega) (fun r h1 h2 => by
          rw [lev_flip2 j hk0.1 hk0.2 (by omega) (by omega) (by omega), if_neg (by tauto)]) k]
        have e0 : lev (flipAt (flipAt j k0) (k0 + 1)) k0 = 1 - lev j k0 := by
          rw [lev_flip2 j hk0.1 hk0.2 (by omega) (by omega) (by omega), if_pos (Or.inl rfl)]
        have e1 : lev (flipAt (flipAt j k0) (k0 + 1)) (k0 + 1) = 1 - lev j (k0 + 1) := by
          rw [lev_flip2 j hk0.1 hk0.2 (by omega) (by omega) (by omega), if_pos (Or.inr rfl)]
        rw [e0, e1]; simp only [eps]


lemma flipAt_invol (m : ℕ) : Function.Involutive (fun σ : Fin K → Fin 2 => flipAt σ m) := by
  intro σ; funext i; simp only [flipAt]; split_ifs <;> simp

lemma card_filter_equiv (m : ℕ) (P Q : (Fin K → Fin 2) → Prop) [DecidablePred P]
    [DecidablePred Q] (h : ∀ σ, P σ ↔ Q (flipAt σ m)) :
    (univ.filter P).card = (univ.filter Q).card :=
  card_equiv (flipAt_invol m).toPerm (fun σ => by simp [h σ])

lemma fcA : ∀ a b c : Fin 2, (a ≠ b ∧ b = c) ↔ (a ≠ b ∧ ¬ b = 1 - c) := by decide
lemma fcB : ∀ a b c : Fin 2, (a ≠ b ∧ b = c) ↔ (a = 1 - b ∧ ¬ 1 - b = c) := by decide
lemma fcC : ∀ a b c : Fin 2, (a = b ∧ ¬ b = c) ↔ (a = b ∧ b = 1 - c) := by decide

lemma card_IStar (K k0 : ℕ) (hk0 : 1 ≤ k0) (hk0K : k0 + 2 ≤ K) :
    4 * (IStar K k0).card = 2 ^ K := by
  classical
  set a := fun σ : Fin K → Fin 2 => lev σ k0
  set b := fun σ : Fin K → Fin 2 => lev σ (k0 + 1)
  set c := fun σ : Fin K → Fin 2 => lev σ (k0 + 2)
  have hS1 : IStar K k0 = univ.filter (fun σ => a σ ≠ b σ ∧ b σ = c σ) := rfl
  have e12 : (univ.filter (fun σ => a σ ≠ b σ ∧ b σ = c σ)).card =
      (univ.filter (fun σ => a σ ≠ b σ ∧ ¬ b σ = c σ)).card := by
    apply card_filter_equiv (k0 + 2); intro σ
    simp only [a, b, c, lev_flip1 σ (by omega : 1 ≤ k0 + 2) hk0K, if_true,
      show k0 ≠ k0 + 2 by omega, show k0 + 1 ≠ k0 + 2 by omega, if_false]
    exact fcA _ _ _
  have e13 : (univ.filter (fun σ => a σ ≠ b σ ∧ b σ = c σ)).card =
      (univ.filter (fun σ => a σ = b σ ∧ ¬ b σ = c σ)).card := by
    apply card_filter_equiv (k0 + 1); intro σ
    simp only [a, b, c, lev_flip1 σ (by omega : 1 ≤ k0 + 1) (by omega : k0 + 1 ≤ K), if_true,
      show k0 ≠ k0 + 1 by omega, show k0 + 2 ≠ k0 + 1 by omega, if_false]
    exact fcB _ _ _
  have e34 : (univ.filter (fun σ => a σ = b σ ∧ ¬ b σ = c σ)).card =
      (univ.filter (fun σ => a σ = b σ ∧ b σ = c σ)).card := by
    apply card_filter_equiv (k0 + 2); intro σ
    simp only [a, b, c, lev_flip1 σ (by omega : 1 ≤ k0 + 2) hk0K, if_true,
      show k0 ≠ k0 + 2 by omega, show k0 + 1 ≠ k0 + 2 by omega, if_false]
    exact fcC _ _ _
  have split1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin K → Fin 2)))
    (fun σ => a σ ≠ b σ)
  have split2 := card_filter_add_card_filter_not
    (s := univ.filter (fun σ : Fin K → Fin 2 => a σ ≠ b σ)) (fun σ => b σ = c σ)
  have split3 := card_filter_add_card_filter_not
    (s := univ.filter (fun σ : Fin K → Fin 2 => ¬ a σ ≠ b σ)) (fun σ => b σ = c σ)
  simp only [filter_filter, not_not] at split2 split3
  rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at split1
  rw [hS1]
  have h4 : (univ.filter (fun σ => a σ = b σ ∧ b σ = c σ)).card =
      (univ.filter (fun σ => a σ = b σ ∧ ¬ b σ = c σ)).card := e34.symm
  simp only [ne_eq, not_not] at split1 split2 split3 e12 e13 h4 ⊢
  omega

theorem three_quarter_solution (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (hK : 3 ≤ K) (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K)
    (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k) (hk0K : k0 ≤ K - 2)
    (hmax : max (δ (k0 + 1)) (δ (k0 + 2)) ≤ 2 * δ k0) :
    (∀ σ τ : Fin K → Fin 2, σ ≠ τ → 2 * δ k0 ≤ ‖scenario δ σ - scenario δ τ‖) ∧
    (∃ Jstar : Finset (Fin K → Fin 2), Jstar.card = 3 * 2 ^ (K - 2) ∧
      ∀ j ∈ Jstar, ∃ i ∉ Jstar, ‖scenario δ i - scenario δ j‖ = 2 * δ k0) ∧
    (∀ n : ℕ, 2 ^ K ≤ 4 * n → n < 2 ^ K →
      IsLeast {v : ℝ | ∃ J : Finset (Fin K → Fin 2), J.card = 2 ^ K - n ∧
          ∃ hJ : Jᶜ.Nonempty, v = redCost δ J hJ}
        (((2 : ℝ) ^ K - n) / 2 ^ K * (2 * δ k0))) := by
  have hk0' := hk0; rw [mem_Icc] at hk0'
  have hcard := card_IStar K k0 hk0'.1 (by omega)
  have hpow : 2 ^ K = 4 * 2 ^ (K - 2) := by
    rw [show K = (K - 2) + 2 by omega, pow_add]; simp; ring
  have hIcard : (IStar K k0).card = 2 ^ (K - 2) := by omega
  have hcompl : (IStar K k0)ᶜ.card = 3 * 2 ^ (K - 2) := by
    rw [card_compl, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hIcard]; omega
  have hpart := partner_exists K δ hδ hK k0 hk0 hmin hk0K hmax
  refine ⟨sep K δ hδ k0 hk0 hmin, ⟨(IStar K k0)ᶜ, hcompl, ?_⟩, ?_⟩
  · intro j hj
    obtain ⟨i, hi, he⟩ := hpart j (by simpa using hj)
    exact ⟨i, by simpa using hi, he⟩
  · intro n hn4 hn
    refine ⟨?_, ?_⟩
    · obtain ⟨J, hJsub, hJc⟩ := exists_subset_card_eq (s := (IStar K k0)ᶜ) (n := 2 ^ K - n)
        (by rw [hcompl]; omega)
      have hIne : (IStar K k0).Nonempty := card_pos.1 (by rw [hIcard]; positivity)
      have hJne : Jᶜ.Nonempty := by
        obtain ⟨x, hx⟩ := hIne
        refine ⟨x, mem_compl.2 fun hxJ => ?_⟩
        have := hJsub hxJ; rw [mem_compl] at this; exact this hx
      refine ⟨J, hJc, hJne, ?_⟩
      unfold redCost
      have hterm : ∀ σ ∈ J, (1 / (2 ^ K : ℝ)) * Jᶜ.inf' hJne
          (fun τ => ‖scenario δ σ - scenario δ τ‖) = (1 / (2 ^ K : ℝ)) * (2 * δ k0) := by
        intro σ hσ
        congr 1
        apply le_antisymm
        · have hσI : σ ∉ IStar K k0 := by have := hJsub hσ; rwa [mem_compl] at this
          obtain ⟨i, hi, he⟩ := hpart σ hσI
          have hiJ : i ∈ Jᶜ := mem_compl.2 fun hiJ => by
            have := hJsub hiJ; rw [mem_compl] at this; exact this hi
          refine (inf'_le _ hiJ).trans ?_
          rw [norm_sub_rev, he]
        · apply le_inf'; intro τ hτ
          apply sep K δ hδ k0 hk0 hmin
          rintro rfl; rw [mem_compl] at hτ; exact hτ hσ
      rw [sum_congr rfl hterm, sum_const, hJc, nsmul_eq_mul, Nat.cast_sub hn.le]; push_cast
      ring
    · rintro v ⟨J, hJc, hJ, rfl⟩
      exact redCost_lower_bound K δ hδ k0 hk0 hmin n hn J hJc hJ

theorem example_4_1 (δ : ℕ → ℝ) (h1 : δ 1 = 0.5) (h2 : δ 2 = 0.6) (h3 : δ 3 = 0.7)
    (h4 : δ 4 = 0.9) (h5 : δ 5 = 1.1) (h6 : δ 6 = 1.3) (h7 : δ 7 = 1.6) (h8 : δ 8 = 1.9)
    (h9 : δ 9 = 2.3) (h10 : δ 10 = 2.7) :
    ((∀ k ∈ Finset.Icc 1 10, δ 1 ≤ δ k) ∧ (1 : ℕ) ≤ 10 - 2 ∧ max (δ 2) (δ 3) ≤ 2 * δ 1) ∧
    ∀ n : ℕ, 256 ≤ n → n < 1024 →
      IsLeast {v : ℝ | ∃ J : Finset (Fin 10 → Fin 2), J.card = 2 ^ 10 - n ∧
          ∃ hJ : Jᶜ.Nonempty, v = redCost δ J hJ}
        ((1024 - n : ℝ) / 1024) := by
  have hmin : ∀ k ∈ Finset.Icc 1 10, δ 1 ≤ δ k := by
    intro k hk; rw [mem_Icc] at hk
    obtain ⟨hk1, hk2⟩ := hk
    interval_cases k <;> simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10] <;> norm_num
  have hmax : max (δ 2) (δ 3) ≤ 2 * δ 1 := by rw [h1, h2, h3]; norm_num
  refine ⟨⟨hmin, by norm_num, hmax⟩, ?_⟩
  intro n hn1 hn2
  have hδ : ∀ k ∈ Finset.Icc 1 10, 0 ≤ δ k := fun k hk => by
    have := hmin k hk; rw [h1] at this; linarith
  have := (three_quarter_solution 10 δ hδ (by norm_num) 1 (by simp) hmin (by norm_num) hmax).2.2
    n (by norm_num; omega) (by norm_num; omega)
  have e : ((2 : ℝ) ^ 10 - n) / 2 ^ 10 * (2 * δ 1) = (1024 - n : ℝ) / 1024 := by
    rw [h1]; norm_num
  rw [e] at this; exact this

end ScenarioReduction.BinaryTree

open ScenarioReduction.BinaryTree

theorem solution (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (hK : 3 ≤ K) (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K)
    (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k) (hk0K : k0 ≤ K - 2)
    (hmax : max (δ (k0 + 1)) (δ (k0 + 2)) ≤ 2 * δ k0) :
    (∀ σ τ : Fin K → Fin 2, σ ≠ τ → 2 * δ k0 ≤ ‖scenario δ σ - scenario δ τ‖) ∧
    (∃ Jstar : Finset (Fin K → Fin 2), Jstar.card = 3 * 2 ^ (K - 2) ∧
      ∀ j ∈ Jstar, ∃ i ∉ Jstar, ‖scenario δ i - scenario δ j‖ = 2 * δ k0) ∧
    (∀ n : ℕ, 2 ^ K ≤ 4 * n → n < 2 ^ K →
      IsLeast {v : ℝ | ∃ J : Finset (Fin K → Fin 2), J.card = 2 ^ K - n ∧
          ∃ hJ : Jᶜ.Nonempty, v = redCost δ J hJ}
        (((2 : ℝ) ^ K - n) / 2 ^ K * (2 * δ k0))) := by
  exact three_quarter_solution K δ hδ hK k0 hk0 hmin hk0K hmax
