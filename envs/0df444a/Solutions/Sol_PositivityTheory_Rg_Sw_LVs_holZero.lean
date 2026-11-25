-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.holZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:13:41.34319+00:00
-- url     : https://prove2.me/submissions/7b1dac64-cf8f-4ea5-8721-24f3941f60aa

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_HasFDerivAtInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_Imports
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarDir
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivEqZeroOfVanish
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_fderiv_eq_zero_of_vanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Filter Topology Set Metric Matrix
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs.HolB PositivityTheory.Rg.Sw.LVs.HolC
variable {n : ℕ}
private theorem iteratedFDeriv_eq_zero_of_eq_zero_on_inG {n : ℕ} {Ω : Set (M2 n)} (hΩ : IsOpen Ω) (hG : GSet n ⊆ Ω) (N : ℕ) :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (H : M2 n → V),
      ContDiffOn ℂ ∞ H Ω → (∀ g, InG g → H g = 0) → ∀ g, InG g → iteratedFDeriv ℂ N H g = 0 := by
  induction N with
  | zero =>
    intro V _ _ _ H _ h0 g hg
    ext v
    simp [h0 g hg]
  | succ N ih =>
    intro V _ _ _ H hH h0 g hg
    have hH' := (contDiffOn_infty_iff_fderiv_of_isOpen hΩ).mp hH
    letI : NormedAddCommGroup (M2 n →L[ℂ] V) := ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℂ (M2 n →L[ℂ] V) := ContinuousLinearMap.toNormedSpace
    haveI : SequentialSpace (M2 n) :=
      inferInstanceAs (SequentialSpace ((Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℂ))
    haveI : @CompleteSpace (M2 n →L[ℂ] V) PseudoMetricSpace.toUniformSpace :=
      ContinuousLinearMap.instCompleteSpace
    have e : iteratedFDeriv ℂ N (fun y => fderiv ℂ H y) g = 0 :=
      ih (fun y => fderiv ℂ H y) hH'.2 (fun g' hg' => fderiv_eq_zero_of_vanish hΩ hG hH h0 hg') g hg
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
    have e' := congrArg (continuousMultilinearCurryRightEquiv' ℂ N (M2 n) V).symm e
    exact e'.trans (map_zero _)
end PositivityTheory.Rg.Sw.LVs
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set Metric Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs.HolB PositivityTheory.Rg.Sw.LVs.HolC
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution : HolZero := by
  intro n Ω F hΩ hG hF h0 N g hg
  exact iteratedFDeriv_eq_zero_of_eq_zero_on_inG hΩ hG N F hF (fun g hg => h0 g hg) g hg
end PositivityTheory.Rg.Sw.LVs
