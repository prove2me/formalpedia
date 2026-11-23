-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.mulVec_halfVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:44.809883+00:00
-- url     : https://prove2.me/submissions/9407ee11-95e7-440d-a847-bd4bdb41035f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution {g : ℕ} (M : Matrix (Fin g) (Fin g) ℤ) (k : Fin g → ℤ) :
    M.map (fun x : ℤ => (x : ℝ)) *ᵥ halfVec k = halfVec (M *ᵥ k) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, halfVec, Matrix.map_apply]
  push_cast
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring
end ReciprocityTheory.ChartRestriction.G.Key.Chi
