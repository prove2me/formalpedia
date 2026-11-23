-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.isCompact_symm_image
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:32.577741+00:00
-- url     : https://prove2.me/submissions/44766004-a5e3-4559-bc4d-00ecaf012b2a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero

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
theorem _root_.solution {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} {F : (Fin e → ℂ) → ℝ}
    (hK : IsCompact (tsupport F)) (hKt : tsupport F ⊆ ψ.target) :
    IsCompact (ψ.symm '' tsupport F) :=
  hK.image_of_continuousOn (ψ.continuousOn_symm.mono hKt)
end ReciprocityTheory.AnForm.M.PLAux
