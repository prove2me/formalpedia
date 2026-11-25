-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_aeval_monomial_mul_7a552b775659
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:13:37.152699+00:00
-- url     : https://prove2.me/submissions/ccbb2ef9-62fd-4d6c-8a9b-0f7fef346104

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartRankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartRankAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ'] (z : (Σ k, ι k) → Φ') (j : ∀ k, ι k)
variable {z j}
namespace GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin
theorem _root_.solution (hz : ∀ k, z ⟨k, j k⟩ ≠ 0) (m : (Σ k, ι k) →₀ ℕ) :
    aeval (affCoord z j) (monomial m (1 : Φ)) *
        ∏ k, z ⟨k, j k⟩ ^ (Finsupp.weight (NumbersDVR.blockWeight ι) m k) =
      aeval z (monomial m (1 : Φ)) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m m' hm hm' =>
    rw [← mul_one (1 : Φ), ← monomial_mul, map_mul, map_mul, map_add, ← hm, ← hm']
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring
  | single p n =>
    rw [← X_pow_eq_monomial, map_pow, map_pow, Finsupp.weight_single,
      Fintype.prod_eq_single p.1 (fun k hk => by simp [NumbersDVR.blockWeight, hk])]
    simp only [affCoord, aeval_X, NumbersDVR.blockWeight, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one, div_pow]
    rw [div_mul_cancel₀ _ (pow_ne_zero _ (hz p.1))]
end GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin
