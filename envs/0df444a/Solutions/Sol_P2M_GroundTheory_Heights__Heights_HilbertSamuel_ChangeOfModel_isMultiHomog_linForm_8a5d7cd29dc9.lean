-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ChangeOfModel_isMultiHomog_linForm_8a5d7cd29dc9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:55:41.335347+00:00
-- url     : https://prove2.me/submissions/8bc0f9f4-c50b-4a36-a9f9-0327a9527c5b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PChangeOfModel

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfModel
variable {K : Type} [Fintype K] {ι ι₂ : K → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι₂ k)]
omit [Fintype K] [∀ k, Fintype (ι₂ k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfModel
theorem _root_.solution (A : ∀ k, ι₂ k → ι k → ℤ) (q : Σ k, ι₂ k) :
    IsMultiHomog (linForm A q) (blockDeg q.1) := by
  classical
  intro m hm k
  obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at ht
  have hmt := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
  subst hmt
  obtain ⟨k₀, j⟩ := q
  by_cases hk : k = k₀
  · subst hk
    simp [blockDeg, Finsupp.single_apply]
  · simp [blockDeg, hk]
end GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfModel
