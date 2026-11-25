-- Prove2me | solution 1 for P2M_GlobalTheory_HeckeTwoAB_bound_F__ff0e78d4a637
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:39:20.435277+00:00
-- url     : https://prove2.me/submissions/734b01c4-8376-4010-9f14-51c3d592d449

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABDifferentiableOnSigma
import Theorems.Thm_P2M_GlobalTheory_HeckeTwoAB_norm_F__7009ac4b1b2e
import Theorems.Thm_GlobalTheory_HeckeTwoAB_bound_exp
import Theorems.Thm_GlobalTheory_HeckeTwoC_lg_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoAB
open MeasureTheory GlobalTheory.HeckeTwoC
namespace GlobalTheory.HeckeTwoAB
theorem _root_.solution {ε M : ℝ} (hε : 0 < ε) (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) {σ : ℂ}
    (hc : 1 + 2 * ε ≤ (a + b : ℝ) + 2 * σ.re) (hM : (a + b : ℝ) + 2 * σ.re ≤ M) (t : ℝ) :
    ‖F' a b ν y σ t‖ ≤
      2 * Real.exp (M * |Real.log (abs y)|) * (|Real.log (abs y)| + 1 / ε) * Real.exp (-(1 + ε) * lg (t / y)) := by
  rw [norm_F' a b ν hy]
  have hD : 0 ≤ lg (t / y) := lg_nonneg _
  have h := bound_exp (L0 := Real.log |y|) hc hM hD hε
  have hL : |L y t| ≤ |Real.log (abs y)| + lg (t / y) := by
    unfold L; exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hD])
  have hE2 : Real.exp (-(ε * lg (t / y))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hE2D : Real.exp (-(ε * lg (t / y))) * lg (t / y) ≤ 1 / ε := by
    rw [Real.exp_neg, le_div_iff₀ hε]
    have hp := Real.exp_pos (ε * lg (t / y))
    have := Real.add_one_le_exp (ε * lg (t / y))
    rw [show (Real.exp (ε * lg (t / y)))⁻¹ * lg (t / y) * ε = (ε * lg (t / y)) / Real.exp (ε * lg (t / y)) by
      field_simp]
    rw [div_le_iff₀ hp]; linarith
  have heC : 0 ≤ Real.exp (M * |Real.log (abs y)|) := (Real.exp_pos _).le
  have hE1 : 0 ≤ Real.exp (-(1 + ε) * lg (t / y)) := (Real.exp_pos _).le
  have hE2p : 0 ≤ Real.exp (-(ε * lg (t / y))) := (Real.exp_pos _).le
  have hl0 := abs_nonneg (Real.log |y|)
  calc Real.exp (-((a + b : ℝ) + 2 * σ.re) * L y t) * (2 * |L y t|)
      ≤ Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) * Real.exp (-(ε * lg (t / y))) *
          (2 * (|Real.log (abs y)| + lg (t / y))) :=
        mul_le_mul h (by linarith) (by positivity) (by positivity)
    _ = 2 * Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) *
          (Real.exp (-(ε * lg (t / y))) * |Real.log (abs y)| + Real.exp (-(ε * lg (t / y))) * lg (t / y)) := by ring
    _ ≤ 2 * Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) * (1 * |Real.log (abs y)| + 1 / ε) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right hE2 hl0) hE2D) (by positivity)
    _ = _ := by ring
end GlobalTheory.HeckeTwoAB
