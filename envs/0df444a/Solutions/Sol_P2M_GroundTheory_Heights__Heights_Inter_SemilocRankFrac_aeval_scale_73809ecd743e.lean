-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_aeval_scale_73809ecd743e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:56:04.544321+00:00
-- url     : https://prove2.me/submissions/bab7e94f-b432-4ff1-89f7-d9c5bf468501

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankFracDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocChartRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac
theorem _root_.solution (y : (Σ k, ι k) → Ω) (c : K → Ω) {u : MRing ι} {a : K → ℕ} (hu : IsMultiHomog u a) :
    aeval (fun p => y p * c p.1) u = aeval y u * ∏ k, c k ^ a k := by
  conv_lhs => rw [u.as_sum]
  conv_rhs => rw [u.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, mul_assoc]
  congr 1
  simp only [mul_pow]
  rw [Finsupp.prod_mul]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  show ∏ i, c k ^ m ⟨k, i⟩ = _
  rw [Finset.prod_pow_eq_pow_sum, hu m hm k]
end GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac
