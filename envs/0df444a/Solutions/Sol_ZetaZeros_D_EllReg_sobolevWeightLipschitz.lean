-- Prove2me | solution 1 for ZetaZeros.D.EllReg.sobolevWeightLipschitz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:40:31.453274+00:00
-- url     : https://prove2.me/submissions/4efc88ac-fbad-4ee8-bfc4-cd357f2ebf8d

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeightDiff
import Theorems.Thm_ZetaZeros_D_EllReg_WD_om_shift
import Theorems.Thm_ZetaZeros_D_EllReg_WD_deriv_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
open WD
namespace ZetaZeros.D.EllReg
theorem _root_.solution : WeightDiff := by
  intro d s M hM
  have hN0 : 0 ≤ |(s - 1) / 2| + M / 2 := add_nonneg (abs_nonneg _) (by linarith)
  refine ⟨(|s| + M) * 2 ^ (|(s - 1) / 2| + M / 2), 2 * (|(s - 1) / 2| + M / 2),
    mul_nonneg (add_nonneg (abs_nonneg s) hM) (Real.rpow_nonneg (by norm_num) _), by linarith, ?_⟩
  intro ε hε0 hε1 ξ η
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => om s M ε (η + t • (ξ - η)))
      ((2 * inner ℝ (η + t • (ξ - η)) (ξ - η)) * (s / 2) * (1 + ‖η + t • (ξ - η)‖ ^ 2) ^ (s / 2 - 1) *
          (1 + ε ^ 2 * ‖η + t • (ξ - η)‖ ^ 2) ^ (-(M / 2)) +
        (1 + ‖η + t • (ξ - η)‖ ^ 2) ^ (s / 2) *
          ((ε ^ 2 * (2 * inner ℝ (η + t • (ξ - η)) (ξ - η))) * (-(M / 2)) *
            (1 + ε ^ 2 * ‖η + t • (ξ - η)‖ ^ 2) ^ (-(M / 2) - 1))) t := by
    intro t
    have hγ : HasDerivAt (fun t : ℝ => η + t • (ξ - η)) (ξ - η) t := by
      have := ((hasDerivAt_id' t).smul_const (ξ - η)).const_add η
      rwa [one_smul] at this
    have h1 : HasDerivAt (fun t : ℝ => 1 + ‖η + t • (ξ - η)‖ ^ 2)
        (2 * inner ℝ (η + t • (ξ - η)) (ξ - η)) t :=
      hγ.norm_sq.const_add 1
    have h2 : HasDerivAt (fun t : ℝ => 1 + ε ^ 2 * ‖η + t • (ξ - η)‖ ^ 2)
        (ε ^ 2 * (2 * inner ℝ (η + t • (ξ - η)) (ξ - η))) t :=
      (hγ.norm_sq.const_mul (ε ^ 2)).const_add 1
    have hp1 : (1 + ‖η + t • (ξ - η)‖ ^ 2) ≠ 0 := by positivity
    have hp2 : (1 + ε ^ 2 * ‖η + t • (ξ - η)‖ ^ 2) ≠ 0 := by positivity
    exact (h1.rpow_const (Or.inl hp1)).mul (h2.rpow_const (Or.inl hp2))
  obtain ⟨D, hD⟩ : ∃ D : ℝ → ℝ, ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => om s M ε (η + t • (ξ - η))) (D t) t ∧
      |D t| ≤ (|s| + M) * ‖ξ - η‖ * om (s - 1) M ε (η + t • (ξ - η)) :=
    ⟨_, fun t => ⟨hderiv t, ZetaZeros.D.EllReg.WD.deriv_bound s M ε hM hε0 hε1 _ _⟩⟩
  have hW : ∀ t ∈ Set.Icc (0 : ℝ) 1, om (s - 1) M ε (η + t • (ξ - η)) ≤
      (2 * (1 + ‖ξ - η‖ ^ 2)) ^ (|(s - 1) / 2| + M / 2) * om (s - 1) M ε η := by
    intro t ht
    apply ZetaZeros.D.EllReg.WD.om_shift (s - 1) M ε hM hε0 hε1
    have e : η + t • (ξ - η) - η = t • (ξ - η) := by abel
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  have hcoef : 0 ≤ (|s| + M) * ‖ξ - η‖ := mul_nonneg (add_nonneg (abs_nonneg s) hM) (norm_nonneg _)
  have hbd : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖D t‖ ≤ (|s| + M) * ‖ξ - η‖ *
      ((2 * (1 + ‖ξ - η‖ ^ 2)) ^ (|(s - 1) / 2| + M / 2) * om (s - 1) M ε η) := by
    intro t ht
    rw [Real.norm_eq_abs]
    exact (hD t).2.trans (mul_le_mul_of_nonneg_left (hW t (Set.Ico_subset_Icc_self ht)) hcoef)
  have hmvt : ‖om s M ε (η + (1 : ℝ) • (ξ - η)) - om s M ε (η + (0 : ℝ) • (ξ - η))‖ ≤
      (|s| + M) * ‖ξ - η‖ *
        ((2 * (1 + ‖ξ - η‖ ^ 2)) ^ (|(s - 1) / 2| + M / 2) * om (s - 1) M ε η) * (1 - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (fun t _ => (hD t).1.hasDerivWithinAt) hbd 1
      (Set.right_mem_Icc.2 zero_le_one)
  have e1 : η + (1 : ℝ) • (ξ - η) = ξ := by rw [one_smul]; abel
  have e0 : η + (0 : ℝ) • (ξ - η) = η := by rw [zero_smul, add_zero]
  rw [e1, e0, Real.norm_eq_abs, sub_zero, mul_one] at hmvt
  have hx := norm_nonneg (ξ - η)
  have hA : (2 * (1 + ‖ξ - η‖ ^ 2)) ^ (|(s - 1) / 2| + M / 2) ≤
      2 ^ (|(s - 1) / 2| + M / 2) * (1 + ‖ξ - η‖) ^ (2 * (|(s - 1) / 2| + M / 2)) := by
    rw [Real.rpow_mul (by linarith : (0 : ℝ) ≤ 1 + ‖ξ - η‖), Real.rpow_two,
      ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ (1 + ‖ξ - η‖) ^ 2)]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith) hN0
  have hW0 : 0 ≤ om (s - 1) M ε η := by unfold om; positivity
  calc |om s M ε ξ - om s M ε η|
      ≤ (|s| + M) * ‖ξ - η‖ *
        ((2 * (1 + ‖ξ - η‖ ^ 2)) ^ (|(s - 1) / 2| + M / 2) * om (s - 1) M ε η) := hmvt
    _ ≤ (|s| + M) * ‖ξ - η‖ *
        ((2 ^ (|(s - 1) / 2| + M / 2) * (1 + ‖ξ - η‖) ^ (2 * (|(s - 1) / 2| + M / 2))) *
          om (s - 1) M ε η) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA hW0) hcoef
    _ = _ := by ring
end ZetaZeros.D.EllReg
