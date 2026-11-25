-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_isMultiProjPrime_comap_rename_bb5f689a2f30
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:11:56.134129+00:00
-- url     : https://prove2.me/submissions/b46b4b7f-9b3d-47ae-a6de-209bf267e789

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_isRelevant_iff_1aee41bc5f2d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_rename_weightedHomogeneousComponent_550dd4a17607

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {K K' : Type*} [DecidableEq K] [DecidableEq K'] {ι : K → Type*} {ι' : K' → Type*}
  {j : K → K'} {g : (Σ k, ι k) → (Σ k, ι' k)} (hgj : ∀ v, (g v).1 = j v.1)
include hgj
namespace GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant
theorem _root_.solution (hj : Function.Injective j) (hg : Function.Injective g)
    (hsurj : ∀ w : Σ k, ι' k, w.1 ∈ Set.range j → ∃ v, g v = w) {R : Type*} [CommRing R]
    {P : Ideal (MRing ι' R)} (hP : IsMultiProjPrime P) :
    IsMultiProjPrime (P.comap (rename (R := R) g)) where
  isPrime := haveI := hP.isPrime; Ideal.comap_isPrime _ _
  multiHomog f hf b := by
    rw [Ideal.mem_comap] at hf ⊢
    rw [rename_weightedHomogeneousComponent hgj hj hg]
    exact hP.multiHomog _ hf _
  relevant := by
    rw [isRelevant_iff]
    intro k
    obtain ⟨w, hw, hwP⟩ := (isRelevant_iff P).1 hP.relevant (j k)
    obtain ⟨v, rfl⟩ := hsurj w ⟨k, hw.symm⟩
    refine ⟨v, hj (by rw [← hgj, hw]), ?_⟩
    rw [Ideal.mem_comap, rename_X]
    exact hwP
end GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant
