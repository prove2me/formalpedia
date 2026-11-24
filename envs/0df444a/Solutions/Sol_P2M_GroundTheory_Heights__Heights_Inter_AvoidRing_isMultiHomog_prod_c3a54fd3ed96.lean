-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_prod_c3a54fd3ed96
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:59.554739+00:00
-- url     : https://prove2.me/submissions/63a70451-f03d-43ba-b810-57be488cda69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_mul_92fa4aba8533
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_one_6a94195931fa

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter GroundTheory.Heights₂.Heights.Inter.AvoidRing
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.Inter.AvoidRing
theorem _root_.solution {β : Type*} (s : Finset β) (f : β → MRingOver R ι) (a : β → K → ℕ)
    (h : ∀ b ∈ s, IsMultiHomog (f b) (a b)) : IsMultiHomog (∏ b ∈ s, f b) (∑ b ∈ s, a b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isMultiHomog_one (R := R) (ι := ι))
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    exact isMultiHomog_mul (h b (Finset.mem_insert_self b s))
      (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))
end GroundTheory.Heights₂.Heights.Inter.AvoidRing
