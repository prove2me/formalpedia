-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.real_quad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:16:13.647954+00:00
-- url     : https://prove2.me/submissions/cdf4c807-1ecd-462b-8594-1d75d286b290

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
theorem _root_.solution {g : ℕ} (σ : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → ℝ) :
    ((x ⬝ᵥ (σ.map Complex.im *ᵥ x) : ℝ) : ℂ) =
      star (fun i => (x i : ℂ)) ⬝ᵥ (imC σ *ᵥ fun i => (x i : ℂ)) := by
  simp only [dotProduct, Matrix.mulVec, imC, Matrix.map_apply, Pi.star_apply, Complex.star_def,
    Complex.conj_ofReal, Complex.ofReal_sum, Complex.ofReal_mul]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
