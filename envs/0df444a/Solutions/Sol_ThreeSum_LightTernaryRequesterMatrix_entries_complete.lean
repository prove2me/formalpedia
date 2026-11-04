-- Prove2me | solution 1 for ThreeSum.LightTernaryRequesterMatrix.entries_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:55.254232+00:00
-- url     : https://prove2.me/submissions/60d00d2e-60ff-4edd-991c-e0e0f09bf67f

import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalRequester
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryCarryCode_carryFromCode_code
import Theorems.Thm_ThreeSum_TernaryCarryCode_codeOfCarry_lt
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog



set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRequesterMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightTernaryRequesterMatrix
theorem _root_.solution {μ : ℕ → ℤ} {positions matrix J n U radix : ℕ} {f : ℕ → ℤ}
    (H : Entries μ positions matrix J (2^J) (n*2^J) U radix f)
    {i : ℕ} (hi : i<n) (c : CarryWord J) (hc : ValidCarry c) :
    ∃r<n*2^J, LightTernarySignedRow.Row μ (matrix+r*(J+2)) J (requesterRaw U radix J (f i) c) ∧
      μ (positions+r)=(i : ℤ) := by
  let q := TernaryCarryCode.codeOfCarry c
  have hq : q<2^J := TernaryCarryCode.codeOfCarry_lt c
  have hQ : 0<2^J := pow_pos (by decide) _
  let r := i*2^J+q
  have hr : r<n*2^J := by dsimp [r]; nlinarith
  have hdiv : r/(2^J)=i := by
    dsimp only [r]
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hQ,Nat.div_eq_of_lt hq,Nat.zero_add]
  have hmod : r%(2^J)=q := by simp [r,Nat.add_mod,Nat.mod_eq_of_lt hq]
  refine ⟨r,hr,?_⟩
  have hecarry : TernaryCarryCode.carryFromCode J q=c := TernaryCarryCode.carryFromCode_code hc
  simpa only [hdiv,hmod,hecarry] using H r hr
end ThreeSum.LightTernaryRequesterMatrix
