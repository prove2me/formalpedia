-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.spDiag_mem_sp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:49.497799+00:00
-- url     : https://prove2.me/submissions/c640481a-a04d-4a1f-b1cd-ba1334060111

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
theorem _root_.solution (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) : spDiag U ∈ symplecticGroup (Fin g) ℤ := by

  rw [SymplecticGroup.mem_iff]
  unfold spDiag
  rw [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [← Matrix.transpose_mul]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
