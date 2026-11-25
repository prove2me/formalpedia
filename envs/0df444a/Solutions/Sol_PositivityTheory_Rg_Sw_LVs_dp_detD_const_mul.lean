-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.dp_detD_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:48:57.50381+00:00
-- url     : https://prove2.me/submissions/61584f3e-ff1d-408e-aa68-08051c3ecf7a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (c : ℂ) {F : Matrix ι ι ℂ → ℂ} (hF : ContDiffAt ℂ (Fintype.card ι) F 0) :
    detD (fun T => c * F T) = c * detD F := by
  unfold detD
  have e : iteratedFDeriv ℂ (Fintype.card ι) (fun T => c * F T) 0 =
      c • iteratedFDeriv ℂ (Fintype.card ι) F 0 := by
    simpa only [smul_eq_mul] using iteratedFDeriv_const_smul_apply' (𝕜 := ℂ) (a := c) hF
  rw [e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring
end PositivityTheory.Rg.Sw.LVs
