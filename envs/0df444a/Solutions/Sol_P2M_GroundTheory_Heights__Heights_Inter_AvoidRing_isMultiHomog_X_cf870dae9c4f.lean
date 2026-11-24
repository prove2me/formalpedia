-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_X_cf870dae9c4f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:42.755814+00:00
-- url     : https://prove2.me/submissions/f2cf9daf-e2f3-4f8e-b8a1-13a0f27d5605

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing

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
theorem _root_.solution [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRingOver R ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  have hX : (X ⟨k, i⟩ : MRingOver R ι) = monomial (Finsupp.single ⟨k, i⟩ 1) 1 := rfl
  rw [hX] at hm
  have hm' : m = Finsupp.single ⟨k, i⟩ 1 := Finset.mem_singleton.mp (support_monomial_subset hm)
  subst hm'
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [h]
end GroundTheory.Heights₂.Heights.Inter.AvoidRing
