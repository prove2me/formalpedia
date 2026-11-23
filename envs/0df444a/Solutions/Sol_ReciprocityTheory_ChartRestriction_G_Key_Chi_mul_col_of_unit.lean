-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.mul_col_of_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:51.526605+00:00
-- url     : https://prove2.me/submissions/202d06a4-3d9f-4c7d-b99a-4b1d7400d616

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
theorem _root_.solution {M O : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} {p : Fin g ⊕ Fin g}
    (h : ∀ r, M r p = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r p) (q : Fin g ⊕ Fin g) :
    (O * M) q p = O q p := by

  rw [Matrix.mul_apply]
  simp_rw [h]
  simp [Matrix.one_apply]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
