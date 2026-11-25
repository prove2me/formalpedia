-- Prove2me | solution 1 for P2M_GlobalTheory_HeckeTwoC_continuous_G__26b518ce0d24
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:30:50.741027+00:00
-- url     : https://prove2.me/submissions/b4b96f66-8199-4d30-a9fd-792a01bd9605

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Theorems.Thm_GlobalTheory_HeckeTwoC_continuous_lg
import Theorems.Thm_GlobalTheory_HeckeTwoC_continuous_G

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
open GlobalTheory GlobalTheory.HeckeTwoC
open MeasureTheory
namespace GlobalTheory.HeckeTwoC
theorem _root_.solution (σ : ℂ) : Continuous (G' σ) := by
  have : G' σ = fun t => G σ t * ((lg t : ℂ) * (-2)) := by funext t; unfold G G'; ring
  rw [this]
  exact (continuous_G σ).mul ((Complex.continuous_ofReal.comp continuous_lg).mul continuous_const)
end GlobalTheory.HeckeTwoC
