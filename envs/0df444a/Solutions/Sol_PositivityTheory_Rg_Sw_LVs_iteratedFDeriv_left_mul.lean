-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.iteratedFDeriv_left_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:53.758799+00:00
-- url     : https://prove2.me/submissions/96a178c9-4853-4690-99b9-152307a7d38b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFderivRightTranslation
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate

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
theorem _root_.solution (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (M x : M2 n)
    (hx : M * x ∈ U) (N : ℕ) (v : Fin N → M2 n) :
    iteratedFDeriv ℂ N (fun y => F (M * y)) x v = iteratedFDeriv ℂ N F (M * x) (fun i => M * v i) := by
  let g : M2 n →L[ℂ] M2 n := (LinearMap.mulLeft ℂ M).toContinuousLinearMap
  have hpre : IsOpen (g ⁻¹' U) := hU.preimage g.continuous
  have hx' : x ∈ g ⁻¹' U := hx
  have key := g.iteratedFDerivWithin_comp_right hF hU.uniqueDiffOn hpre.uniqueDiffOn hx' (i := N)
    (by exact_mod_cast le_top)
  have e1 : iteratedFDerivWithin ℂ N (F ∘ g) (g ⁻¹' U) x = iteratedFDeriv ℂ N (F ∘ g) x :=
    iteratedFDerivWithin_of_isOpen N hpre hx'
  have e2 : iteratedFDerivWithin ℂ N F U (g x) = iteratedFDeriv ℂ N F (g x) :=
    iteratedFDerivWithin_of_isOpen N hU hx
  have key2 : iteratedFDeriv ℂ N (F ∘ g) x =
      (iteratedFDeriv ℂ N F (g x)).compContinuousLinearMap fun _ => g := by
    rw [← e1, ← e2]
    exact key
  have hfg : (fun y => F (M * y)) = F ∘ g := rfl
  rw [hfg, key2]
  rfl
end PositivityTheory.Rg.Sw.LVs
