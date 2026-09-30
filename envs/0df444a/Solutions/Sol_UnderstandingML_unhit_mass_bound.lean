-- Prove2me | solution 1 for UnderstandingML.unhit_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T07:21:26.119652+00:00
-- url     : https://prove2.me/submissions/865ca248-1d3a-46c0-84d1-1f4bba6b1c55

import Definitions.Def_UnderstandingML_NearestNeighbor
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory

namespace UnhitAux

lemma mass_bound (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) (hm : 0 < m) :
    p * (1 - p) ^ m ≤ 1 / (m * Real.exp 1) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (1 - p) ^ m ≤ Real.exp (-p) ^ m := by
    apply pow_le_pow_left₀ (by linarith)
    have := Real.add_one_le_exp (-p); linarith
  have h2 : Real.exp (-p) ^ m = Real.exp (-(p * m)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have h3 : p * m ≤ Real.exp (p * m - 1) := by
    have := Real.add_one_le_exp (p * m - 1); linarith
  have h4 : p * Real.exp (-(p * m)) ≤ 1 / (m * Real.exp 1) := by
    rw [le_div_iff₀ (by positivity)]
    calc p * Real.exp (-(p * m)) * (m * Real.exp 1)
        = (p * m) * Real.exp (-(p * m - 1)) := by
          rw [show -(p * m - 1) = -(p * m) + 1 by ring, Real.exp_add]; ring
      _ ≤ Real.exp (p * m - 1) * Real.exp (-(p * m - 1)) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  calc p * (1 - p) ^ m ≤ p * Real.exp (-p) ^ m := mul_le_mul_of_nonneg_left h1 hp0
    _ = p * Real.exp (-(p * m)) := by rw [h2]
    _ ≤ _ := h4

end UnhitAux

open UnderstandingML in
open Classical in
theorem solution {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    {r : ℕ} (C : Fin r → Set X) (hC : ∀ i, MeasurableSet (C i)) (m : ℕ) (hm : 0 < m) :
    ∫ S, ∑ i, (if ∀ j, S j ∉ C i then (D (C i)).toReal else 0) ∂(iidLaw D m) ≤
      r / (m * Real.exp 1) := by
  have hA : ∀ i, MeasurableSet {S : Fin m → X | ∀ j, S j ∉ C i} := by
    intro i
    have : {S : Fin m → X | ∀ j, S j ∉ C i} = Set.univ.pi (fun _ ↦ (C i)ᶜ) := by
      ext S; simp
    rw [this]; exact MeasurableSet.univ_pi (fun _ ↦ (hC i).compl)
  have hprob : ∀ i, (iidLaw D m {S | ∀ j, S j ∉ C i}).toReal = (1 - (D (C i)).toReal) ^ m := by
    intro i
    have : {S : Fin m → X | ∀ j, S j ∉ C i} = Set.univ.pi (fun _ ↦ (C i)ᶜ) := by
      ext S; simp
    rw [this, iidLaw, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ENNReal.toReal_pow, prob_compl_eq_one_sub (hC i), ENNReal.toReal_sub_of_le prob_le_one
        ENNReal.one_ne_top]
    simp
  have : IsProbabilityMeasure (iidLaw D m) := by
    unfold iidLaw; infer_instance
  have heach : ∀ i, ∫ S, (if ∀ j, S j ∉ C i then (D (C i)).toReal else 0) ∂(iidLaw D m) =
      (D (C i)).toReal * (1 - (D (C i)).toReal) ^ m := by
    intro i
    have : (fun S : Fin m → X ↦ if ∀ j, S j ∉ C i then (D (C i)).toReal else 0) =
        Set.indicator {S | ∀ j, S j ∉ C i} (fun _ ↦ (D (C i)).toReal) := by
      ext S; simp [Set.indicator]
    rw [this, integral_indicator_const _ (hA i), smul_eq_mul, measureReal_def, hprob, mul_comm]
  rw [integral_finsetSum]
  · simp_rw [heach]
    calc ∑ i, (D (C i)).toReal * (1 - (D (C i)).toReal) ^ m
        ≤ ∑ _i : Fin r, 1 / (m * Real.exp 1) := by
          apply Finset.sum_le_sum; intro i _
          exact UnhitAux.mass_bound _ ENNReal.toReal_nonneg
            (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (s := C i))) m hm
      _ = r / (m * Real.exp 1) := by simp [div_eq_mul_inv]
  · intro i _
    have : (fun S : Fin m → X ↦ if ∀ j, S j ∉ C i then (D (C i)).toReal else 0) =
        Set.indicator {S | ∀ j, S j ∉ C i} (fun _ ↦ (D (C i)).toReal) := by
      ext S; simp [Set.indicator]
    rw [this]
    exact Integrable.indicator (integrable_const _) (hA i)
