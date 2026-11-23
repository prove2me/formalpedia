-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.colsFixed_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:50.945799+00:00
-- url     : https://prove2.me/submissions/c6e31666-922d-4373-9f99-957b86ed0b07

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol

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
theorem _root_.solution (k : ℕ) : ColsFixed k (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) := by
  intro i _
  exact ⟨fun r => rfl, fun r => rfl⟩
end ReciprocityTheory.ChartRestriction.G.Key.Chi
