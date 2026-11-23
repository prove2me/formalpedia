-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.spDiag_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:49.573799+00:00
-- url     : https://prove2.me/submissions/213729de-c939-4d7b-a36d-17321765855c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SpGenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) : spDiag U ∈ spH g := Submonoid.subset_closure (Set.mem_union_left _ (Set.mem_union_right _ ⟨U, rfl⟩))
end ReciprocityTheory.ChartRestriction.G.Key.Chi
