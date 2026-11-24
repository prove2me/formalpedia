-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_prod_pow_5715147e4abb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:24.368727+00:00
-- url     : https://prove2.me/submissions/30008709-6ac1-4b98-a514-8ec066f3cfaa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*}
    [CommRing R] (i : ∀ k, ι k) (n : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, i k⟩ : MRing ι R) ^ n k) n := by
  have h := IsWeightedHomogeneous.prod (R := R) Finset.univ
    (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ n k) (fun k => n k • blockWeight ι ⟨k, i k⟩)
    (w := blockWeight ι) (fun k _ => (isWeightedHomogeneous_X R _ _).pow _)
  have hs : (∑ k, n k • blockWeight ι ⟨k, i k⟩) = n := by
    funext j
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [hs] at h
  exact h
end GroundTheory.Heights₂.Heights.FieldNumbers
