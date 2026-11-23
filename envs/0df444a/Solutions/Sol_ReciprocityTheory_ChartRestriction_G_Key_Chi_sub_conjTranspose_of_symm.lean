-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.sub_conjTranspose_of_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:01.916276+00:00
-- url     : https://prove2.me/submissions/12562edc-6d78-4931-b461-77a38512030e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_Blocks
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm

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
theorem _root_.solution {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm) :
    τ - τᴴ = (2 * I) • imC τ := by
  ext i j
  have h : τ j i = τ i j := by simpa using congrFun (congrFun hτ i) j
  simp only [Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, imC, Matrix.map_apply, h,
    smul_eq_mul]
  apply Complex.ext <;> simp <;> ring
end ReciprocityTheory.ChartRestriction.G.Key.Chi
