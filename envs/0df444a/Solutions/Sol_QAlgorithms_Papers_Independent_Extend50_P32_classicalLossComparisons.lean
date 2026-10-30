-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P32.classicalLossComparisons
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:13:47.579863+00:00
-- url     : https://prove2.me/submissions/2182743f-244c-4d5a-ba80-1b76c58fc1bb

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P32
noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Matrix ComplexOrder Topology

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P32

open QAlgorithms.Papers.Independent.Support50.P38 (wordMass tv)

open QAlgorithms.Papers.Independent.Gap20.P17 (HasSpectrum)

lemma q172_term {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal ((Real.sqrt a - Real.sqrt b) ^ 2) ≤ chiTerm a b := by
  unfold chiTerm
  by_cases hb0 : b = 0
  · subst hb0
    by_cases ha0 : a = 0
    · subst ha0; simp
    · simp [ha0]
  · simp only [hb0, if_false]
    apply ENNReal.ofReal_le_ofReal
    have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    rw [le_div_iff₀ hbpos]
    have hsa := Real.sq_sqrt ha
    have hsb := Real.sq_sqrt hb
    have h1 : (a - b) ^ 2 = (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 := by
      rw [show (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2
        = ((Real.sqrt a) ^ 2 - (Real.sqrt b) ^ 2) ^ 2 by ring, hsa, hsb]
    have h2 : b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
      nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)

lemma q172_h2 {d : ℕ} (k : ℕ) (a b : Fin d → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ENNReal.ofReal (h2 k a b) ≤ chi2 k a b := by
  unfold h2 chi2
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by split_ifs <;> positivity)]
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact q172_term (ha i) (hb i)
  · simp

lemma q172_klterm {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≠ 0 → b ≠ 0) :
    (if a = 0 then 0 else a * Real.log (a / b)) ≤ (if b = 0 then 0 else (a - b) ^ 2 / b) + (a - b) := by
  by_cases ha0 : a = 0
  · subst ha0
    by_cases hb0 : b = 0
    · subst hb0; simp
    · simp only [hb0, if_true, if_false]
      have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      field_simp
      ring_nf; rfl
  · have hb0 := hab ha0
    have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    simp only [ha0, hb0, if_false]
    have hl := Real.log_le_sub_one_of_pos (div_pos hapos hbpos)
    have : a * Real.log (a / b) ≤ a * (a / b - 1) := mul_le_mul_of_nonneg_left hl ha
    have e : a * (a / b - 1) = (a - b) ^ 2 / b + (a - b) := by field_simp; ring
    linarith

theorem solution {d : ℕ} (hd : 0 < d) (alpha beta : Fin d → ℝ)
    (hAlpha : Learning.IsDistribution alpha) (hBeta : Learning.IsDistribution beta)
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    ENNReal.ofReal (h2 d alpha beta) ≤ chi2 d alpha beta ∧
    ENNReal.ofReal (h2 k alpha beta) ≤ chi2 k alpha beta ∧
    kl alpha beta ≤ chi2 d alpha beta := by
  refine ⟨q172_h2 d _ _ hAlpha.1 hBeta.1, q172_h2 k _ _ hAlpha.1 hBeta.1, ?_⟩
  unfold kl
  split_ifs with hex
  · obtain ⟨i, hai, hbi⟩ := hex
    have : chi2 d alpha beta = ⊤ := by
      unfold chi2
      rw [ENNReal.sum_eq_top]
      exact ⟨i, Finset.mem_univ _, by simp [i.isLt, chiTerm, hai, hbi]⟩
    rw [this]
  · push Not at hex
    have hchi : chi2 d alpha beta = ENNReal.ofReal
        (∑ i, if beta i = 0 then 0 else (alpha i - beta i) ^ 2 / beta i) := by
      unfold chi2
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by
        split_ifs
        · exact le_refl _
        · exact div_nonneg (sq_nonneg _) (hBeta.1 i))]
      apply Finset.sum_congr rfl
      intro i _
      simp only [i.isLt, if_true, chiTerm]
      by_cases hb0 : beta i = 0
      · have : alpha i = 0 := by
          by_contra h; exact hex i h hb0
        simp [hb0, this]
      · simp [hb0]
    rw [hchi]
    apply ENNReal.ofReal_le_ofReal
    have := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      q172_klterm (hAlpha.1 i) (hBeta.1 i) (fun h hb => hex i h hb))
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hAlpha.2, hBeta.2] at this
    linarith
