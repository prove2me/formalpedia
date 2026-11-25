-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.word_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:31:43.524706+00:00
-- url     : https://prove2.me/submissions/269182bf-d509-4aa5-8d0b-91cb136eaa2e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CcTMulQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_EvalZeroReplicateAppend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {ι : Type}
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
theorem _root_.solution (l : ι) (Ls : List ι) (m : ι →₀ ℕ) :
    word (l :: Ls) m = List.replicate (m l) l ++ word Ls m := by
  simp only [word, List.flatMap_cons]
end ReciprocityTheory.ChartRestriction.G.TB.G2
