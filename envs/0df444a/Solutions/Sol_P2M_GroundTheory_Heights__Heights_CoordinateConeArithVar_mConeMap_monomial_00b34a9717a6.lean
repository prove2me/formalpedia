-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mConeMap_monomial_00b34a9717a6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:52:43.687576+00:00
-- url     : https://prove2.me/submissions/f6f85621-3533-41d9-8a2b-8adb615a27f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.CoordinateConeArithVar
theorem _root_.solution (y : (Σ k, ι k) → Ω) (e : (Σ k, ι k) →₀ ℕ) (a : ℤ) :
    mConeMap y (monomial e a) =
      monomial (e.mapDomain Sigma.fst) ((a : Ω) * e.prod fun p n ↦ y p ^ n) := by
  rw [mConeMap, aeval_monomial, monomial_eq, map_mul, mul_assoc]
  congr 1
  · have h1 : (e.prod fun p n ↦ (C (y p) * X p.1 : MvPolynomial K Ω) ^ n) =
        (e.prod fun p n ↦ C (y p ^ n)) * e.prod fun p n ↦ (X p.1 : MvPolynomial K Ω) ^ n := by
      rw [← Finsupp.prod_mul]
      refine Finsupp.prod_congr fun p _ ↦ ?_
      rw [mul_pow, map_pow]
    rw [h1, Finsupp.prod_mapDomain_index (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _)]
    congr 1
    rw [map_finsuppProd]
end GroundTheory.Heights₂.Heights.CoordinateConeArithVar
