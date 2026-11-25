-- Prove2me | solution 1 for P2M_GlobalTheory_HeckeTwoC_norm_G__1a9e454f2caf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:31:05.156285+00:00
-- url     : https://prove2.me/submissions/219da37a-4c3c-4e92-852f-7cbe733afaf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Theorems.Thm_GlobalTheory_HeckeTwoC_lg_nonneg
import Theorems.Thm_GlobalTheory_HeckeTwoC_norm_G

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
theorem _root_.solution (σ : ℂ) (t : ℝ) : ‖G' σ t‖ = Real.exp (-(2 + 2 * σ.re) * lg t) * (2 * lg t) := by
  have : G' σ t = G σ t * ((lg t : ℂ) * (-2)) := by unfold G G'; ring
  rw [this, norm_mul, norm_G, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (lg_nonneg t)]
  simp; ring
end GlobalTheory.HeckeTwoC
