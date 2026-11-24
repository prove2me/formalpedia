-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_isMultiHomog_prod_X_pow_104a77d0415d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:13.627151+00:00
-- url     : https://prove2.me/submissions/7f130ff8-4fde-4ffd-9776-2837604da214

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogFirstCoordinate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution [DecidableEq K] {J : Type*} [Fintype J] (q : J → Σ k, ι k) (e : J → ℕ) :
    IsMultiHomog (∏ j, X (q j) ^ e j : MRing ι)
      (fun k => ∑ j ∈ Finset.univ.filter (fun j => (q j).1 = k), e j) := by
  classical
  have hm : (∏ j, X (q j) ^ e j : MRing ι) = monomial (∑ j, Finsupp.single (q j) (e j)) 1 := by
    rw [monomial_sum_one]
    simp [X_pow_eq_monomial]
  intro m hm' k
  rw [hm] at hm'
  have := Finset.mem_singleton.1 (support_monomial_subset hm')
  subst this
  beta_reduce
  rw [Finset.sum_filter]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨k0, i0⟩ := q j
  by_cases h : k0 = k
  · subst h
    simp [Finsupp.single_apply]
  · simp [h]
end GroundTheory.Heights₂.Heights.Inter
