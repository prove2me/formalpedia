-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.spTransl_mem_sp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:00.46562+00:00
-- url     : https://prove2.me/submissions/6bc098d5-389c-4b54-9aaa-ed2057be5a6b

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
theorem _root_.solution {S : Matrix (Fin g) (Fin g) ℤ} (hS : S.IsSymm) :
    spTransl S ∈ symplecticGroup (Fin g) ℤ := by

  rw [SymplecticGroup.mem_iff]
  have hS' : Sᵀ = S := hS
  unfold spTransl
  rw [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hS']
end ReciprocityTheory.ChartRestriction.G.Key.Chi
