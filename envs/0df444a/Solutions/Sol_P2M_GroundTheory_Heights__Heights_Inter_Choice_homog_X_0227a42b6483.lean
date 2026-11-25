-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_X_0227a42b6483
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:13:43.316729+00:00
-- url     : https://prove2.me/submissions/ea0633e7-bc4e-4c77-892d-6452dae9507c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChoice

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.Choice
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
open Classical
namespace GroundTheory.Heights₂.Heights.Inter.Choice
theorem _root_.solution (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRingOver R ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  have hm' : m = Finsupp.single ⟨k, i⟩ 1 := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hm) (by rw [MvPolynomial.coeff_X]; simp [Ne.symm h])
  subst hm'
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, this, h, Pi.single_apply]
end GroundTheory.Heights₂.Heights.Inter.Choice
