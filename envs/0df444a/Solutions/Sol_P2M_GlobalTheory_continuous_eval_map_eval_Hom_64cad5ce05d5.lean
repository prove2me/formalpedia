-- Prove2me | solution 1 for P2M_GlobalTheory_continuous_eval_map_eval_Hom_64cad5ce05d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:11:15.576939+00:00
-- url     : https://prove2.me/submissions/f18f5597-ab8d-41b7-8daa-ece65119e011

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsEmbeddingsOverInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type*} [CommRing K] (sg : K →+* ℂ) {D : ℕ}
    (μ : Polynomial (MvPolynomial (Fin D) K)) (x : ℂ) :
    Continuous fun z : Fin D → ℂ => (μ.map (MvPolynomial.eval₂Hom sg z)).eval x := by
  simp only [Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  refine continuous_finsetSum _ fun i _ => Continuous.mul ?_ continuous_const
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map]
  exact MvPolynomial.continuous_eval _
end GlobalTheory
