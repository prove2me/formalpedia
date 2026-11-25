-- Prove2me | solution 1 for P2M_GlobalTheory_HeckeTwoAB_norm_F__7009ac4b1b2e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:30:30.866275+00:00
-- url     : https://prove2.me/submissions/efed8272-a603-417a-9d22-aae1bd15ecca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABDifferentiableOnSigma
import Theorems.Thm_GlobalTheory_HeckeTwoAB_norm_F

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
theorem _root_.solution (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) (σ : ℂ) (t : ℝ) :
    ‖F' a b ν y σ t‖ = Real.exp (-((a + b : ℝ) + 2 * σ.re) * L y t) * (2 * |L y t|) := by
  have : F' a b ν y σ t = F a b ν y σ t * ((L y t : ℂ) * (-2)) := by unfold F F'; ring
  rw [this, norm_mul, norm_F a b ν hy, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  simp; ring
end GlobalTheory.HeckeTwoAB
