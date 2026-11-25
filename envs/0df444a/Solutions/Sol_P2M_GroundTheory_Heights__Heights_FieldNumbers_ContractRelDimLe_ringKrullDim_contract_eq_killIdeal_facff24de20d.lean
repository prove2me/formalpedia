-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_ringKrullDim_contract_eq_killIdeal_facff24de20d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:05:17.911975+00:00
-- url     : https://prove2.me/submissions/e94421ac-1b0d-43f1-bc0c-5d75be436df5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsContractRelDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PContractRelDimLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_killBlocks_compl_rename_cd9002839356
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_exists_rename_eq_killBlocks_compl_af2a3d137dd5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_comp_f21ab6d300e7


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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe
variable {K K' : Type*} [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K'] {F : Type*}
  [Field F] (j : K ↪ K') (ι' : K' → Type*)
namespace GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe
theorem _root_.solution (P' : Ideal (MRing ι' F)) :
    ringKrullDim (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') =
      ringKrullDim (MRing ι' F ⧸ killIdeal P' (Finset.univ.map j)ᶜ) := by
  set f : MRing (fun k => ι' (j k)) F →+* MRing ι' F ⧸ killIdeal P' (Finset.univ.map j)ᶜ :=
    (Ideal.Quotient.mk _).comp (rename (blockIncl j ι')).toRingHom
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := exists_rename_eq_killBlocks_compl j ι' (F := F) x
    refine ⟨a, ?_⟩
    change Ideal.Quotient.mk _ (rename (blockIncl j ι') a) = _
    rw [Ideal.Quotient.eq, ha]
    change killBlocks _ (killBlocks _ x - x) ∈ P'
    rw [map_sub, ← AlgHom.comp_apply, killBlocks_comp le_rfl, sub_self]
    exact P'.zero_mem
  have hker : RingHom.ker f = contractPrime j P' := by
    ext a
    change Ideal.Quotient.mk _ (rename (blockIncl j ι') a) = 0 ↔ rename (blockIncl j ι') a ∈ P'
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change killBlocks _ (rename (blockIncl j ι') a) ∈ P' ↔ _
    rw [← AlgHom.comp_apply, killBlocks_compl_rename]
  rw [← hker]
  exact ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hsurj)
end GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe
