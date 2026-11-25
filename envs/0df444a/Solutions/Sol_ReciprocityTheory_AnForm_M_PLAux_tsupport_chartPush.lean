-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.tsupport_chartPush
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:23.066976+00:00
-- url     : https://prove2.me/submissions/f023e4e0-69f7-4445-9815-f266345e132b

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_chartPush_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_isCompact_symm_image

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.PLAux
theorem _root_.solution [T2Space X] (ψ : OpenPartialHomeomorph X (Fin e → ℂ))
    {F : (Fin e → ℂ) → ℝ} (hK : IsCompact (tsupport F)) (hKt : tsupport F ⊆ ψ.target) :
    tsupport (chartPush ψ F) ⊆ ψ.symm '' tsupport F := by
  refine closure_minimal (fun p hp => ?_) (isCompact_symm_image hK hKt).isClosed
  by_contra h
  exact hp (chartPush_eq_zero ψ h)
end ReciprocityTheory.AnForm.M.PLAux
