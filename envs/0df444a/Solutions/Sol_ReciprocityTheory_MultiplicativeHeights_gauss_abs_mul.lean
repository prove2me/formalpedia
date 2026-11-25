-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gauss_abs_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:33:31.768662+00:00
-- url     : https://prove2.me/submissions/fe546d3e-e5cf-4c4d-9daf-082b8d3222f6

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_Lemmata_GeneralBFactLeftExtra_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_mul_of_monomial_order

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open NumberField
variable {K : Type*} [Field K] [NumberField K] {σ : Type*}
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution [Fintype σ] (w : FinitePlace K)
    (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :
    gaussAbs w (f * g) = gaussAbs w f * gaussAbs w g := by
  let _ : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  have : WellFoundedGT σ := Finite.to_wellFoundedGT
  exact gauss_abs_mul_of_monomial_order MonomialOrder.lex w f g hf hg
end ReciprocityTheory.MultiplicativeHeights
