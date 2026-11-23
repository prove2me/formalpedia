-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.re_pos_of_posDef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:04.38588+00:00
-- url     : https://prove2.me/submissions/aa109d54-722e-4bea-8a91-99d52e586077

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
theorem _root_.solution {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) {v : Fin g → ℂ}
    (hv : v ≠ 0) : 0 < (star v ⬝ᵥ (Y.map (fun x : ℝ => (x : ℂ)) *ᵥ v)).re := by
  set x : Fin g → ℝ := fun i => (v i).re with hxdef
  set y : Fin g → ℝ := fun i => (v i).im with hydef
  have key : (star v ⬝ᵥ (Y.map (fun x : ℝ => (x : ℂ)) *ᵥ v)).re = x ⬝ᵥ (Y *ᵥ x) + y ⬝ᵥ (Y *ᵥ y) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Complex.re_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, hxdef, hydef]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.mul_re, Complex.mul_im]
  have hnn : ∀ z : Fin g → ℝ, 0 ≤ z ⬝ᵥ (Y *ᵥ z) := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · have := hY.dotProduct_mulVec_pos hz
      simp only [star_trivial] at this
      exact this.le
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hv
    funext i
    apply Complex.ext
    · exact congrFun hc.1 i
    · exact congrFun hc.2 i
  rw [key]
  rcases hxy with h | h
  · have := hY.dotProduct_mulVec_pos h
    simp only [star_trivial] at this
    linarith [hnn y]
  · have := hY.dotProduct_mulVec_pos h
    simp only [star_trivial] at this
    linarith [hnn x]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
