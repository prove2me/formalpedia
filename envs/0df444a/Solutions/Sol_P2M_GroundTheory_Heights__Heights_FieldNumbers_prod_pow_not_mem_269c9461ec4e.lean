-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_prod_pow_not_mem_269c9461ec4e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:07:24.784008+00:00
-- url     : https://prove2.me/submissions/4f20e113-0f20-4490-a9b6-7f02827fae8c

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
theorem _root_.solution {K : Type} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]
    (P : Ideal (MRing ι R)) [hP : P.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι R) ∉ P) (n : K → ℕ) :
    (∏ k, (X ⟨k, i k⟩ : MRing ι R) ^ n k) ∉ P := by
  intro h
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hi k (hP.mem_of_pow_mem _ hk)
end GroundTheory.Heights₂.Heights.FieldNumbers
