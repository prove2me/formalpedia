-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameMultiProjPrime_proof_175cae7f6f64
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:36:42.024197+00:00
-- url     : https://prove2.me/submissions/c6f938f3-651c-43b7-b041-b43113c28f33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiProjPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameMultiProjPrime_rename_weightedHomogeneousComponent_a0f8e609218b

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
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace RenameMultiProjPrime
theorem _root_.solution : RenameMultiProjPrime.Statement.{u} := by
  intro R _ S K' _ _ κ ι' E σ hσ P hP
  refine ⟨?_, ?_, ?_⟩
  · have := hP.isPrime
    exact Ideal.comap_isPrime _ _
  · intro f hf b
    rw [Ideal.mem_comap] at hf ⊢
    rw [RenameMultiProjPrime.rename_weightedHomogeneousComponent (R := R) E σ hσ b f]
    exact hP.multiHomog _ hf _
  · intro s
    obtain ⟨i', hi'⟩ := hP.relevant (E s)
    obtain ⟨⟨s', i⟩, hv⟩ : ∃ v, σ v = ⟨E s, i'⟩ := σ.surjective _
    have hs : s' = s := E.injective (by simpa [hv] using (hσ ⟨s', i⟩).symm)
    subst hs
    refine ⟨i, ?_⟩
    rw [Ideal.mem_comap, rename_X, hv]
    exact hi'
end RenameMultiProjPrime
end GroundTheory.Heights₂.Heights.FieldNumbers
