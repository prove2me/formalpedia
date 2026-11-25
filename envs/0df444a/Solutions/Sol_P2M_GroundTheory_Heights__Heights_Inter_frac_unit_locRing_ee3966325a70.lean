-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_frac_unit_locRing_ee3966325a70
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:32.626342+00:00
-- url     : https://prove2.me/submissions/4d8af579-97ff-4588-8150-b21d809c638e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_XcNotMemOfIsRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TwoMemFunFieldSpecZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LogCardLocIdealUnitMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_frac_mem_locRing_a3c1c87b7867

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {P W : Ideal (MRing ι)} (hPW : P ≤ W) {u v : MRing ι} {a : K → ℕ}
    (hu : IsMultiHomog u a) (hv : IsMultiHomog v a) (huW : u ∉ W) (hvW : v ∉ W) [P.IsPrime]
    {y : FractionRing (MRing ι ⧸ P)}
    (hy : y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)) :
    y ∈ locRing P W ∧ ∃ z ∈ locRing P W, y * z = 1 := by
  have hu0 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => huW (hPW h)
  have hv0 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => hvW (hPW h)
  set z := algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) /
    algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)
  refine ⟨frac_mem_locRing hPW hu hv hvW hy, z, frac_mem_locRing hPW hv hu huW (div_mul_cancel₀ _ hu0), ?_⟩
  rw [mul_div_assoc', hy, div_self hu0]
end GroundTheory.Heights₂.Heights.Inter
