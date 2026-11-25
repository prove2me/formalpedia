-- Prove2me | solution 1 for P2M_GlobalTheory_HeckeTwoAB_continuous_F__ed6efc273c97
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:32:02.969595+00:00
-- url     : https://prove2.me/submissions/4d90c609-c298-4ec6-9f6b-509407b8a55c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABDifferentiableOnSigma
import Theorems.Thm_GlobalTheory_HeckeTwoAB_continuous_L
import Theorems.Thm_GlobalTheory_HeckeTwoAB_continuous_F

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
theorem _root_.solution (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) (σ : ℂ) : Continuous (F' a b ν y σ) := by
  have : F' a b ν y σ = fun t => F a b ν y σ t * ((L y t : ℂ) * (-2)) := by funext t; unfold F F'; ring
  rw [this]
  exact (continuous_F a b ν hy σ).mul ((Complex.continuous_ofReal.comp continuous_L).mul continuous_const)
end GlobalTheory.HeckeTwoAB
