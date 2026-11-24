-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_chartHom_mul_d94a61c7c2a6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:27.846964+00:00
-- url     : https://prove2.me/submissions/7705429e-7cea-4da3-896e-58bfec564462

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsFunFieldMulEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_chartHom_coe_900b030d0f63

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
theorem _root_.solution {P : Ideal (MRing ι)} (j : ∀ k, ι k) (r : (Σ k, ι k) → funField P)
    (hr : ∀ p : Σ k, ι k, (r p : FractionRing (MRing ι ⧸ P)) * toFrac P (X ⟨p.1, j p.1⟩) = toFrac P (X p))
    {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    (chartHom r f : FractionRing (MRing ι ⧸ P)) * toFrac P (∏ k, (X ⟨k, j k⟩ : MRing ι) ^ a k) = toFrac P f := by
  classical
  rw [chartHom_coe]
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hdeg := hf μ hμ
  rw [monomial_eq, map_mul, map_mul, mul_assoc]
  congr 1
  · simp
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [map_prod, map_pow, coe_eval₂Hom, eval₂_X]
  have hm : ∏ k, toFrac P (X ⟨k, j k⟩) ^ a k = ∏ p : Σ k, ι k, toFrac P (X ⟨p.1, j p.1⟩) ^ μ p := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hdeg k]
    exact (Finset.prod_pow_eq_pow_sum _ _ _).symm
  rw [hm, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← mul_pow, hr]
end GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
