-- Prove2me | solution 2 for RegLearnGames.IndivRegret.oftrl_stability
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:34:40.090763+00:00
-- url     : https://prove2.me/submissions/f1a580f8-0e0a-4800-8439-c0d65f3918b6

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting
set_option autoImplicit false

open RegLearnGames.TotalRegret

lemma rl_l1_smul {d : ℕ} (c : ℝ) (v : Fin d → ℝ) : l1 (c • v) = |c| * l1 v := by
  unfold l1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [abs_mul]

lemma rl_l1_nonneg {d : ℕ} (v : Fin d → ℝ) : 0 ≤ l1 v :=
  Finset.sum_nonneg (fun i _ => abs_nonneg _)

lemma rl_l1_neg {d : ℕ} (v : Fin d → ℝ) : l1 (-v) = l1 v := by
  have := rl_l1_smul (-1) v
  simpa using this

lemma rl_dot_le {d : ℕ} (x y : Fin d → ℝ) : x ⬝ᵥ y ≤ l1 x * ‖y‖ := by
  unfold l1 dotProduct
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  calc x i * y i ≤ |x i * y i| := le_abs_self _
    _ = |x i| * |y i| := abs_mul _ _
    _ ≤ |x i| * ‖y‖ := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have := norm_le_pi_norm y i
        simpa using this

lemma rl_dyadic {d : ℕ} (R : (Fin d → ℝ) → ℝ)
    (hR : ∀ a ∈ stdSimplex ℝ (Fin d), ∀ b ∈ stdSimplex ℝ (Fin d),
      R ((1 / 2 : ℝ) • (a + b)) ≤ (R a + R b) / 2 - (l1 (a - b)) ^ 2 / 8)
    (a b : Fin d → ℝ) (ha : a ∈ stdSimplex ℝ (Fin d)) (hb : b ∈ stdSimplex ℝ (Fin d)) :
    ∀ k : ℕ, ((1 - (1 / 2 : ℝ) ^ k) • a + ((1 / 2 : ℝ) ^ k) • b ∈ stdSimplex ℝ (Fin d)) ∧
      R ((1 - (1 / 2 : ℝ) ^ k) • a + ((1 / 2 : ℝ) ^ k) • b) ≤
        ((1 / 2 : ℝ) ^ k) * R b + (1 - (1 / 2 : ℝ) ^ k) * R a -
          (1 / 2) * ((1 / 2 : ℝ) ^ k) * (1 - (1 / 2 : ℝ) ^ k) * (l1 (a - b)) ^ 2 := by
  intro k
  induction k with
  | zero =>
    simp only [pow_zero, sub_self, zero_smul, one_smul, zero_add]
    refine ⟨hb, ?_⟩
    simp
  | succ k ih =>
    obtain ⟨hmem, hle⟩ := ih
    have hp0 : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
    have hp1 : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hid : (1 / 2 : ℝ) • (a + ((1 - (1 / 2 : ℝ) ^ k) • a + ((1 / 2 : ℝ) ^ k) • b))
        = (1 - (1 / 2 : ℝ) ^ (k + 1)) • a + ((1 / 2 : ℝ) ^ (k + 1)) • b := by
      rw [pow_succ]
      module
    have hmem2 : (1 - (1 / 2 : ℝ) ^ (k + 1)) • a + ((1 / 2 : ℝ) ^ (k + 1)) • b ∈ stdSimplex ℝ (Fin d) := by
      have hp1' : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      exact (convex_stdSimplex ℝ (Fin d)) ha hb (by linarith) (by positivity) (by ring)
    refine ⟨hmem2, ?_⟩
    have h1 := hR a ha _ hmem
    rw [hid] at h1
    have h2 : a - ((1 - (1 / 2 : ℝ) ^ k) • a + ((1 / 2 : ℝ) ^ k) • b) = ((1 / 2 : ℝ) ^ k) • (a - b) := by
      module
    rw [h2, rl_l1_smul, abs_of_nonneg hp0] at h1
    have h3 : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2 : ℝ) ^ k / 2 := by rw [pow_succ]; ring
    rw [h3] at h1 ⊢
    set p := (1 / 2 : ℝ) ^ k
    nlinarith [h1, hle]

lemma rl_strong {d : ℕ} (R : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (hR : ∀ a ∈ stdSimplex ℝ (Fin d), ∀ b ∈ stdSimplex ℝ (Fin d),
      R ((1 / 2 : ℝ) • (a + b)) ≤ (R a + R b) / 2 - (l1 (a - b)) ^ 2 / 8)
    (c w g : Fin d → ℝ) (hw : w ∈ stdSimplex ℝ (Fin d)) (hg : g ∈ stdSimplex ℝ (Fin d))
    (hopt : ∀ v ∈ stdSimplex ℝ (Fin d), v ⬝ᵥ c - R v / η ≤ w ⬝ᵥ c - R w / η) :
    (l1 (w - g)) ^ 2 / (2 * η) ≤ (R g - R w) / η - (g - w) ⬝ᵥ c := by
  have hk : ∀ k : ℕ, (l1 (w - g)) ^ 2 / (2 * η) * (1 - (1 / 2 : ℝ) ^ k) ≤ (R g - R w) / η - (g - w) ⬝ᵥ c := by
    intro k
    obtain ⟨hmem, hle⟩ := rl_dyadic R hR w g hw hg k
    have h1 := hopt _ hmem
    set p := (1 / 2 : ℝ) ^ k with hp
    have hp0 : 0 < p := by positivity
    have hdot : ((1 - p) • w + p • g) ⬝ᵥ c = w ⬝ᵥ c + p * ((g - w) ⬝ᵥ c) := by
      simp only [add_dotProduct, smul_dotProduct, sub_dotProduct, smul_eq_mul]
      ring
    rw [hdot] at h1
    have h2 : R ((1 - p) • w + p • g) / η ≤
        (p * R g + (1 - p) * R w - (1 / 2) * p * (1 - p) * (l1 (w - g)) ^ 2) / η :=
      div_le_div_of_nonneg_right hle hη.le
    have h3 : 0 ≤ p * ((R g - R w) / η - (g - w) ⬝ᵥ c) - (1 / (2 * η)) * p * (1 - p) * (l1 (w - g)) ^ 2 := by
      have e : (p * R g + (1 - p) * R w - (1 / 2) * p * (1 - p) * (l1 (w - g)) ^ 2) / η
          = p * R g / η + (1 - p) * R w / η - (1 / (2 * η)) * p * (1 - p) * (l1 (w - g)) ^ 2 := by
        field_simp
      have e2 : p * ((R g - R w) / η) = p * R g / η - p * R w / η := by ring
      have e3 : (1 - p) * R w / η = R w / η - p * R w / η := by ring
      nlinarith [h1, h2, e, e2, e3]
    have h4 : 0 ≤ ((R g - R w) / η - (g - w) ⬝ᵥ c) - (1 / (2 * η)) * (1 - p) * (l1 (w - g)) ^ 2 := by
      have : 0 ≤ p * (((R g - R w) / η - (g - w) ⬝ᵥ c) - (1 / (2 * η)) * (1 - p) * (l1 (w - g)) ^ 2) := by
        nlinarith [h3]
      exact (mul_nonneg_iff_of_pos_left hp0).1 this
    have e4 : (l1 (w - g)) ^ 2 / (2 * η) * (1 - p) = (1 / (2 * η)) * (1 - p) * (l1 (w - g)) ^ 2 := by ring
    linarith
  by_contra hcon
  push_neg at hcon
  set X := (l1 (w - g)) ^ 2 / (2 * η) with hX
  set Y := (R g - R w) / η - (g - w) ⬝ᵥ c
  have hX0 : 0 ≤ X := by positivity
  have hpos : 0 < X - Y := by linarith
  obtain ⟨k, hk'⟩ := exists_pow_lt_of_lt_one (show 0 < (X - Y) / (X + 1) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have := hk k
  have h5 : X * (1 / 2 : ℝ) ^ k < X - Y := by
    calc X * (1 / 2 : ℝ) ^ k ≤ (X + 1) * (1 / 2 : ℝ) ^ k := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ < (X + 1) * ((X - Y) / (X + 1)) := by
          apply mul_lt_mul_of_pos_left hk' (by positivity)
      _ = X - Y := by field_simp
  nlinarith

lemma rl_key {d : ℕ} (R : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (hR : ∀ a ∈ stdSimplex ℝ (Fin d), ∀ b ∈ stdSimplex ℝ (Fin d),
      R ((1 / 2 : ℝ) • (a + b)) ≤ (R a + R b) / 2 - (l1 (a - b)) ^ 2 / 8)
    (c c' w w' : Fin d → ℝ) (hw : w ∈ stdSimplex ℝ (Fin d)) (hw' : w' ∈ stdSimplex ℝ (Fin d))
    (hopt : ∀ v ∈ stdSimplex ℝ (Fin d), v ⬝ᵥ c - R v / η ≤ w ⬝ᵥ c - R w / η)
    (hopt' : ∀ v ∈ stdSimplex ℝ (Fin d), v ⬝ᵥ c' - R v / η ≤ w' ⬝ᵥ c' - R w' / η) :
    l1 (w - w') ≤ η * ‖c - c'‖ := by
  have h1 := rl_strong R η hη hR c w w' hw hw' hopt
  have h2 := rl_strong R η hη hR c' w' w hw' hw hopt'
  have hl : l1 (w' - w) = l1 (w - w') := by
    rw [← rl_l1_neg (w - w')]; congr 1; abel
  rw [hl] at h2
  set D := l1 (w - w') with hD
  have hD0 : 0 ≤ D := rl_l1_nonneg _
  have hdot : (w - w') ⬝ᵥ (c - c') ≤ D * ‖c - c'‖ := rl_dot_le _ _
  have e1 : (w' - w) ⬝ᵥ c = -((w - w') ⬝ᵥ c) := by
    rw [← neg_sub, neg_dotProduct]
  have e2 : (w - w') ⬝ᵥ (c - c') = (w - w') ⬝ᵥ c - (w - w') ⬝ᵥ c' := by
    rw [dotProduct_sub]
  have h3 : D ^ 2 / η ≤ D * ‖c - c'‖ := by
    have : D ^ 2 / (2 * η) + D ^ 2 / (2 * η) = D ^ 2 / η := by field_simp; ring
    rw [← this]
    have e3 : (R w' - R w) / η + (R w - R w') / η = 0 := by ring
    linarith
  rcases hD0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have : D ^ 2 ≤ η * (D * ‖c - c'‖) := by
      rw [div_le_iff₀ hη] at h3; linarith
    nlinarith

lemma rl_Icc_eq {d : ℕ} (u : ℕ → Fin d → ℝ) (t : ℕ) :
    ∑ s ∈ Finset.Icc 1 t, u s = ∑ s ∈ Finset.Ico 1 (t + 1), u s := by
  rw [Finset.Ico_add_one_right_eq_Icc]

lemma rl_Ico_succ {d : ℕ} (u : ℕ → Fin d → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    ∑ s ∈ Finset.Ico 1 (t + 1), u s = ∑ s ∈ Finset.Ico 1 t, u s + u t :=
  Finset.sum_Ico_succ_top ht _

theorem solution {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (h𝓡 : IsOneStronglyConvexL1 𝓡) (u w : ℕ → Fin d → ℝ)
    (hu : ∀ t x, u t x ∈ Set.Icc (0 : ℝ) 1)
    (hw : IsOFTRL 𝓡 η (fun T => u (T - 1)) u w) :
    ∀ t, l1 (w t - w (t + 1)) ≤ 2 * η := by
  have hR := h𝓡.2
  have hnorm : ∀ v : Fin d → ℝ, (∀ x, |v x| ≤ 1) → ‖v‖ ≤ 1 := by
    intro v hv
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro x; simpa using hv x
  intro t
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have h := rl_key 𝓡 η hη hR 0 (∑ s ∈ Finset.Ico 1 1, u s + u (1 - 1)) (w 0) (w 1) hw.1.1
      (hw.2 1 le_rfl).1
      (by
        intro v hv
        simp only [dotProduct_zero, zero_sub, neg_le_neg_iff]
        exact div_le_div_of_nonneg_right (hw.1.2 v hv) hη.le)
      (hw.2 1 le_rfl).2
    have hn : ‖(0 : Fin d → ℝ) - (∑ s ∈ Finset.Ico 1 1, u s + u (1 - 1))‖ ≤ 1 := by
      apply hnorm
      intro x
      simp only [Finset.Ico_self, Finset.sum_empty, zero_add, zero_sub, Pi.neg_apply, abs_neg]
      rw [abs_of_nonneg (hu 0 x).1]
      exact (hu 0 x).2
    have : η * ‖(0 : Fin d → ℝ) - (∑ s ∈ Finset.Ico 1 1, u s + u (1 - 1))‖ ≤ η * 1 :=
      mul_le_mul_of_nonneg_left hn hη.le
    linarith
  · have h := rl_key 𝓡 η hη hR ((∑ s ∈ Finset.Ico 1 t, u s) + u (t - 1))
      ((∑ s ∈ Finset.Ico 1 (t + 1), u s) + u (t + 1 - 1)) (w t) (w (t + 1))
      (hw.2 t ht).1 (hw.2 (t + 1) (by omega)).1 (hw.2 t ht).2 (hw.2 (t + 1) (by omega)).2
    have e : ((∑ s ∈ Finset.Ico 1 t, u s) + u (t - 1)) - ((∑ s ∈ Finset.Ico 1 (t + 1), u s) + u (t + 1 - 1))
        = u (t - 1) - (2 : ℝ) • u t := by
      rw [rl_Ico_succ u t ht]
      simp only [Nat.add_sub_cancel]
      module
    rw [e] at h
    have hn : ‖u (t - 1) - (2 : ℝ) • u t‖ ≤ 2 := by
      rw [pi_norm_le_iff_of_nonneg (by norm_num)]
      intro x
      have h1 := hu (t - 1) x
      have h2 := hu t x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
      rw [abs_le]
      constructor <;> push_cast <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have : η * ‖u (t - 1) - (2 : ℝ) • u t‖ ≤ η * 2 := mul_le_mul_of_nonneg_left hn hη.le
    linarith
