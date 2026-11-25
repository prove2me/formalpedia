-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.colsFixed_spPJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:15:26.881331+00:00
-- url     : https://prove2.me/submissions/03ad0590-2e7f-4a33-bf26-e2f4e72ab403

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
theorem _root_.solution {k : ℕ} (j : Fin g) (hj : k ≤ (j : ℕ)) : ColsFixed k (spPJ j) := by
  intro i hi
  have hij : j ≠ i := fun h => by subst h; omega
  refine ⟨fun r => ?_, fun r => ?_⟩ <;> rcases r with r | r <;>
    simp [spPJ, Matrix.single_apply, Matrix.one_apply, hij]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
