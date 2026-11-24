-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.iteratedFDeriv_mul_const_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:47.636182+00:00
-- url     : https://prove2.me/submissions/680dfbf2-87b6-460f-ae9f-a8f4f6f6103e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFDerivMulConstOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (c : ℂ)
    (x : M2 n) (hx : x ∈ U) (N : ℕ) (v : Fin N → M2 n) :
    iteratedFDeriv ℂ N (fun y => F y * c) x v = iteratedFDeriv ℂ N F x v * c := by
  have hFx : ContDiffAt ℂ ∞ F x := hF.contDiffAt (hU.mem_nhds hx)
  have h := ContinuousLinearMap.iteratedFDeriv_comp_left ((ContinuousLinearMap.mul ℂ ℂ).flip c) hFx
    (i := N) (by exact_mod_cast le_top)
  have e : (fun y => F y * c) = (ContinuousLinearMap.mul ℂ ℂ).flip c ∘ F := by funext y; rfl
  rw [e, h]; rfl
end PositivityTheory.Rg.Sw.LVs
