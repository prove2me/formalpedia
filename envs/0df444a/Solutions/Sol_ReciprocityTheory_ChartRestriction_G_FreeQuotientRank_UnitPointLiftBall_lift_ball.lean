-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall.lift_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:01:08.575084+00:00
-- url     : https://prove2.me/submissions/1be0d72f-9aee-46c8-a590-58b7999c8a05

import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsTorusPointOneLeNormSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_UnitPointLiftBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall
open MvPolynomial ReciprocityTheory.MultiplicativeHeights
variable {K : Type*} [NormedField K] [IsUltrametricDist K] {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall
theorem _root_.solution (P : MvPolynomial ι K) (hP : ∀ μ, ‖coeff μ P‖ ≤ 1) :
    ∃ PO : MvPolynomial ι (unitBallRing K), MvPolynomial.map (unitBallRing K).subtype PO = P := by
  have hmem : P ∈ Set.range (MvPolynomial.map (unitBallRing K).subtype) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨μ, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hc
    refine ⟨⟨coeff μ P, ?_⟩, rfl⟩
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
    exact_mod_cast hP μ
  obtain ⟨PO, hPO⟩ := hmem
  exact ⟨PO, hPO⟩
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall
