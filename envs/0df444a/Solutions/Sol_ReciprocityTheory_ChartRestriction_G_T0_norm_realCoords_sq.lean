-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.norm_realCoords_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:38:29.206734+00:00
-- url     : https://prove2.me/submissions/3e549efb-7c89-4f0e-8a37-fbf551c1473b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulEmbeddingColumns
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecSmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_inner_hRe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_star_dotProduct_self_re

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
theorem _root_.solution (x : (K →+* ℂ) → Fin r → ℂ) : ‖hRe x‖ ^ 2 = ∑ σ, hns (x σ) := by
  rw [← real_inner_self_eq_norm_sq, inner_hRe, Complex.re_sum]
  exact Finset.sum_congr rfl fun σ _ => star_dotProduct_self_re _
end ReciprocityTheory.ChartRestriction.G.T0
