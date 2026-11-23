-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.spTransl_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:47.7728+00:00
-- url     : https://prove2.me/submissions/36e16c71-0efb-4494-8c31-6cf6e87d328b

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
theorem _root_.solution {S : Matrix (Fin g) (Fin g) ℤ} (hS : S.IsSymm) : spTransl S ∈ spH g := Submonoid.subset_closure (Set.mem_union_left _ (Set.mem_union_left _ ⟨S, hS, rfl⟩))
end ReciprocityTheory.ChartRestriction.G.Key.Chi
