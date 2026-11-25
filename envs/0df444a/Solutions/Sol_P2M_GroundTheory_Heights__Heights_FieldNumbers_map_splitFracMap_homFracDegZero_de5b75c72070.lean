-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_map_splitFracMap_homFracDegZero_de5b75c72070
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:38:42.934983+00:00
-- url     : https://prove2.me/submissions/7261cbdb-b4a6-4d79-b03b-ff9776643cca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_splitFracMap_mk_90d3ee9fcc29
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_rename_splitVar_symm_aa89fdc4ec16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_equiv_zero_fbc06038a4c0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameMultiHomog_proof_0a47e7848016
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_splitVarEquiv_fst_fb4410ce5862


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
variable {F : Type u} [Field F] {K K' : Type} (j : K ↪ K') {ι' : K' → Type}
  (P' : Ideal (MRing ι' F)) [P'.IsPrime]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution [DecidableEq K] [DecidableEq K'] :
    (homFracDegZero (splitPrime j P')).map (splitFracMap j P') = homFracDegZero P' := by
  set E := splitBlockEquiv j
  set σ := splitVarEquiv j ι'
  have hσ : ∀ v, (σ v).1 = E v.1 := splitVarEquiv_fst j ι'
  have hσ' : ∀ v, (σ.symm v).1 = E.symm v.1 := fun v => by
    rw [Equiv.eq_symm_apply, ← hσ, Equiv.apply_symm_apply]
  unfold homFracDegZero
  rw [IntermediateField.adjoin_map]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨b, f, g, hf, hg, hgQ, rfl⟩, rfl⟩
    refine ⟨b ∘ E.symm, rename (splitVar j ι') f, rename (splitVar j ι') g, ?_, ?_, hgQ, ?_⟩
    · have := RenameMultiHomog.proof F _ K' E.toEmbedding _ ι' σ hσ f b hf
      rwa [Equiv.coe_toEmbedding, extend_equiv_zero] at this
    · have := RenameMultiHomog.proof F _ K' E.toEmbedding _ ι' σ hσ g b hg
      rwa [Equiv.coe_toEmbedding, extend_equiv_zero] at this
    · rw [map_div₀, splitFracMap_mk, splitFracMap_mk]
  · rintro ⟨b, f, g, hf, hg, hgP, rfl⟩
    refine ⟨_, ⟨b ∘ E, rename σ.symm f, rename σ.symm g, ?_, ?_, ?_, rfl⟩, ?_⟩
    · have := RenameMultiHomog.proof F K' _ E.symm.toEmbedding ι' _ σ.symm hσ' f b hf
      rwa [Equiv.coe_toEmbedding, extend_equiv_zero, Equiv.symm_symm] at this
    · have := RenameMultiHomog.proof F K' _ E.symm.toEmbedding ι' _ σ.symm hσ' g b hg
      rwa [Equiv.coe_toEmbedding, extend_equiv_zero, Equiv.symm_symm] at this
    · show rename (splitVar j ι') (rename σ.symm g) ∉ P'
      rwa [rename_splitVar_symm]
    · rw [map_div₀, splitFracMap_mk, splitFracMap_mk, rename_splitVar_symm, rename_splitVar_symm]
end GroundTheory.Heights₂.Heights.FieldNumbers
