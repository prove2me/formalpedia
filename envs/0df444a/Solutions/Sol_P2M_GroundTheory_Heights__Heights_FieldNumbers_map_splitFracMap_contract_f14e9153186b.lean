-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_map_splitFracMap_contract_f14e9153186b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:01:30.802863+00:00
-- url     : https://prove2.me/submissions/5f33e740-58fa-4fbf-bcdc-8d2041317e7e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_contractPrime_inl_iff_20c191697d9f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_splitFracMap_contractFracMap_inl_mk_c258701bd505

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
    ((homFracDegZero (contractPrime (Function.Embedding.inl : K ↪ K ⊕ blockCompl j)
        (splitPrime j P'))).map (contractFracMap Function.Embedding.inl (splitPrime j P'))).map
        (splitFracMap j P') =
      (homFracDegZero (contractPrime j P')).map (contractFracMap j P') := by
  rw [IntermediateField.map_map]
  unfold homFracDegZero
  rw [IntermediateField.adjoin_map, IntermediateField.adjoin_map]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨b, f, g, hf, hg, hgQ, rfl⟩, rfl⟩
    refine ⟨_, ⟨b, f, g, hf, hg, ?_, rfl⟩, ?_⟩
    · exact fun h => hgQ ((mem_contractPrime_inl_iff j P' g).mpr h)
    · simp only [AlgHom.comp_apply, map_div₀]
      exact (congrArg₂ (· / ·) (splitFracMap_contractFracMap_inl_mk j P' f)
        (splitFracMap_contractFracMap_inl_mk j P' g)).symm
  · rintro ⟨_, ⟨b, f, g, hf, hg, hgP, rfl⟩, rfl⟩
    refine ⟨_, ⟨b, f, g, hf, hg, ?_, rfl⟩, ?_⟩
    · exact fun h => hgP ((mem_contractPrime_inl_iff j P' g).mp h)
    · simp only [AlgHom.comp_apply, map_div₀]
      exact congrArg₂ (· / ·) (splitFracMap_contractFracMap_inl_mk j P' f)
        (splitFracMap_contractFracMap_inl_mk j P' g)
end GroundTheory.Heights₂.Heights.FieldNumbers
