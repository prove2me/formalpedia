-- Prove2me | solution 1 for UnderstandingML.adaboost_reweighted_error
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T15:43:32.909663+00:00
-- url     : https://prove2.me/submissions/da588ad7-c50f-4c51-963e-85ef1f6b9116

import Definitions.Def_UnderstandingML_Boosting


open MeasureTheory

namespace UnderstandingML

section ReweightedErrorProof

variable {X : Type*} {m : ℕ}

lemma adaDist_nonneg_sum_one (hm : 0 < m) (S : Fin m → X × Bool) (h : ℕ → X → Bool) (t : ℕ) :
    (∀ i, 0 ≤ adaDist S h t i) ∧ ∑ i, adaDist S h t i = 1 := by
  induction t with
  | zero =>
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    refine ⟨fun i ↦ by simp [adaDist], ?_⟩
    simp [adaDist, hm']
  | succ t ih =>
    obtain ⟨hnn, hsum⟩ := ih
    set w := adaWeight (weightedError (adaDist S h t) S (h t))
    have hZ : 0 < ∑ j, adaDist S h t j * Real.exp (-(w * sgn (S j).2 * sgn (h t (S j).1))) := by
      obtain ⟨j, hj⟩ : ∃ j, 0 < adaDist S h t j := by
        by_contra hcon
        push Not at hcon
        have : ∑ i, adaDist S h t i ≤ 0 := Finset.sum_nonpos fun i _ ↦ hcon i
        linarith
      exact lt_of_lt_of_le (mul_pos hj (Real.exp_pos _))
        (Finset.single_le_sum (f := fun j ↦ adaDist S h t j *
          Real.exp (-(w * sgn (S j).2 * sgn (h t (S j).1))))
          (fun i _ ↦ mul_nonneg (hnn i) (Real.exp_pos _).le) (Finset.mem_univ j))
    refine ⟨fun i ↦ ?_, ?_⟩
    · exact div_nonneg (mul_nonneg (hnn i) (Real.exp_pos _).le) hZ.le
    · change ∑ i, adaDist S h t i * Real.exp (-(w * sgn (S i).2 * sgn (h t (S i).1))) /
        ∑ j, adaDist S h t j * Real.exp (-(w * sgn (S j).2 * sgn (h t (S j).1))) = 1
      rw [← Finset.sum_div, div_self hZ.ne']

end ReweightedErrorProof

/-- **Exercise 10.3** (p. 143). The error of `hₜ` with respect to the updated distribution
`D⁽ᵗ⁺¹⁾` is exactly `1/2`: `∑ᵢ Dᵢ⁽ᵗ⁺¹⁾ 𝟙[yᵢ ≠ hₜ(xᵢ)] = 1/2`. Stated for a nonempty sample and
`εₜ ∈ (0, 1)`, where the weight `wₜ` is defined. -/
theorem adaboost_reweighted_error {X : Type*} {m : ℕ} (hm : 0 < m) (S : Fin m → X × Bool)
    (h : ℕ → X → Bool) (t : ℕ) (hε : 0 < adaError S h t ∧ adaError S h t < 1) :
    weightedError (adaDist S h (t + 1)) S (h t) = 1 / 2 := by
  obtain ⟨hnn, hsum⟩ := adaDist_nonneg_sum_one hm S h t
  set D := adaDist S h t with hD
  set ε := adaError S h t with hεdef
  have hεD : weightedError D S (h t) = ε := rfl
  set w := adaWeight ε with hw
  -- the ± product is `1` on correct examples and `-1` on mistakes
  have hsg : ∀ i, sgn (S i).2 * sgn (h t (S i).1) =
      if h t (S i).1 = (S i).2 then 1 else -1 := by
    intro i
    cases (S i).2 <;> cases h t (S i).1 <;> simp [sgn]
  have hfac : ∀ i, Real.exp (-(w * sgn (S i).2 * sgn (h t (S i).1))) =
      (if h t (S i).1 = (S i).2 then 0 else 1) * Real.exp w +
      (1 - (if h t (S i).1 = (S i).2 then 0 else 1)) * Real.exp (-w) := by
    intro i
    rw [mul_assoc, hsg i]
    split_ifs <;> simp
  -- sums over the sample
  have hsumε : ∑ i, D i * (if h t (S i).1 = (S i).2 then 0 else 1) = ε := hεD
  have hZ : ∑ j, D j * Real.exp (-(w * sgn (S j).2 * sgn (h t (S j).1))) =
      ε * Real.exp w + (1 - ε) * Real.exp (-w) := by
    simp only [hfac, mul_add, Finset.sum_add_distrib]
    rw [← hsumε]
    have : ∑ x, D x * ((1 - if h t (S x).1 = (S x).2 then (0:ℝ) else 1) * Real.exp (-w)) =
        (∑ x, D x - ∑ x, D x * (if h t (S x).1 = (S x).2 then (0:ℝ) else 1)) *
          Real.exp (-w) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      ring
    rw [this, hsum, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    ring
  have hnum : ∑ i, D i * Real.exp (-(w * sgn (S i).2 * sgn (h t (S i).1))) *
      (if h t (S i).1 = (S i).2 then 0 else 1) = ε * Real.exp w := by
    rw [← hsumε, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hfac i]
    split_ifs <;> simp
  -- `e^{2w} = 1/ε − 1`
  have he2 : Real.exp w * Real.exp w = 1 / ε - 1 := by
    rw [← Real.exp_add, hw, adaWeight, show 1 / 2 * Real.log (1 / ε - 1) +
      1 / 2 * Real.log (1 / ε - 1) = Real.log (1 / ε - 1) by ring]
    apply Real.exp_log
    have : 1 < 1 / ε := by rw [lt_div_iff₀ hε.1]; linarith [hε.2]
    linarith
  have hew := Real.exp_pos w
  have hkey : ε * Real.exp w = (1 - ε) * Real.exp (-w) := by
    have h1 : ε * (Real.exp w * Real.exp w) = 1 - ε := by
      rw [he2, mul_sub, mul_one_div_cancel hε.1.ne', mul_one]
    rw [Real.exp_neg, eq_mul_inv_iff_mul_eq₀ hew.ne']
    linarith [h1]
  have hZpos : 0 < ε * Real.exp w + (1 - ε) * Real.exp (-w) :=
    add_pos (mul_pos hε.1 hew) (mul_pos (by linarith [hε.2]) (Real.exp_pos _))
  change ∑ i, (D i * Real.exp (-(w * sgn (S i).2 * sgn (h t (S i).1))) /
      ∑ j, D j * Real.exp (-(w * sgn (S j).2 * sgn (h t (S j).1)))) *
      (if h t (S i).1 = (S i).2 then 0 else 1) = 1 / 2
  simp only [div_mul_eq_mul_div]
  rw [← Finset.sum_div, hnum, hZ, ← hkey]
  have : 0 < ε * Real.exp w := mul_pos hε.1 hew
  rw [div_eq_iff (by linarith)]
  ring

end UnderstandingML

open UnderstandingML in
theorem solution {X : Type*} {m : ℕ} (hm : 0 < m) (S : Fin m → X × Bool)
    (h : ℕ → X → Bool) (t : ℕ) (hε : 0 < adaError S h t ∧ adaError S h t < 1) :
    weightedError (adaDist S h (t + 1)) S (h t) = 1 / 2 :=
  UnderstandingML.adaboost_reweighted_error hm S h t hε
