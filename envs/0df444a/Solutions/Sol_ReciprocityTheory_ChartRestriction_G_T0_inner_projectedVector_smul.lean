-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.inner_projectedVector_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:37:23.008886+00:00
-- url     : https://prove2.me/submissions/d487cfef-7cce-422a-a739-4fa624c78939

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulEmbeddingColumns
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecSmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_inner_hRe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_orthogonalProjector_mulVec_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField ComplexConjugate NumberField.ComplexEmbedding
open scoped ComplexOrder
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (b : Fin k → Fin r → K) (a a' : K) (x y : Fin r → K) :
    inner ℝ (hpv b (a • x)) (hpv b (a' • y)) =
      (∑ σ : K →+* ℂ, conj (σ a) * σ a' *
        (star (hPm σ b *ᵥ fun l => σ (x l)) ⬝ᵥ (hPm σ b *ᵥ fun l => σ (y l)))).re := by
  rw [hpv, hpv, inner_hRe]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [orthogonalProjector_mulVec_smul, orthogonalProjector_mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, Complex.star_def]
  ring
end ReciprocityTheory.ChartRestriction.G.T0
