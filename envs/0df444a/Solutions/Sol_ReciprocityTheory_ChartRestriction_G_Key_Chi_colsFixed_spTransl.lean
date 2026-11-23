-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.colsFixed_spTransl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:03.732824+00:00
-- url     : https://prove2.me/submissions/f80999b9-76dd-4b5c-b3a2-dd2eda13d6a0

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
theorem _root_.solution {k : ℕ} {S : Matrix (Fin g) (Fin g) ℤ}
    (hS : ∀ i : Fin g, (i : ℕ) < k → ∀ l, S l i = 0) : ColsFixed k (spTransl S) := by
  intro i hi
  refine ⟨fun r => ?_, fun r => ?_⟩ <;> rcases r with r | r <;>
    simp [spTransl, Matrix.one_apply, hS i hi]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
