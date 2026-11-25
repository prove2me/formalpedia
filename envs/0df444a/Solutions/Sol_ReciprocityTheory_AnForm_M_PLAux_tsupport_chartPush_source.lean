-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.tsupport_chartPush_source
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:14:01.892137+00:00
-- url     : https://prove2.me/submissions/417d6f2e-b802-4371-923f-3b4866b60417

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_tsupport_chartPush

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
    tsupport (chartPush ψ F) ⊆ ψ.source := by
  refine (tsupport_chartPush ψ hK hKt).trans ?_
  rintro _ ⟨y, hy, rfl⟩
  exact ψ.map_target (hKt hy)
end ReciprocityTheory.AnForm.M.PLAux
