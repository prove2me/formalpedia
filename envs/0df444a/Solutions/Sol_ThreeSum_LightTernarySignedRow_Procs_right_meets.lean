-- Prove2me | solution 1 for ThreeSum.LightTernarySignedRow.Procs.right_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:36:56.246369+00:00
-- url     : https://prove2.me/submissions/de20a0af-157c-4196-b439-34cd8e914bab

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
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
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Definitions.Def_WeightedCache3SUM_Alias_5d4b5ec466dc091a
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
import Theorems.Thm_ThreeSum_TernarySignedReduction_shiftTwo_cast
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
open ThreeSum ThreeSum.LightTernarySignedRow
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernarySignedRow
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ→ℤ} {J radix dst work U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+2<lim.depth) (hb : 1≤radix)
    (hC : |c|≤(U : ℤ)) (hsep : dst+J+2≤work)
    (hspace : space work (3*U)≤lim.space) (hword : (word (3*U) radix J : ℤ)≤lim.word) :
    Meets lim P pMain d [c,2*U,1,J,radix,dst,work,0,1] μ (time J (3*U))
      (fun _ ν => Row ν dst J (rightRaw U radix J c) ∧ Kept μ ν dst) := by
  have hs := shiftTwo_cast hC
  have hU : (0 : ℤ)≤U := by positivity
  have hbounds := abs_le.mp hC
  have hv : shiftTwo U c≤3*U := by exact_mod_cast (by omega : (shiftTwo U c : ℤ)≤3*U)
  have hh := S.meets (μ := μ) hw hd hb hv (by push_cast; omega) (hC.trans (by omega))
    (by omega : 2*U≤3*U) (by norm_num : |(1 : ℤ)|≤1)
    (by norm_num : |(0 : ℤ)|≤1) (by norm_num : |(1 : ℤ)|≤1) hsep hspace hword
  apply hh.mono le_rfl
  rintro r ν ⟨hread,ht0,ht1,hkeep⟩
  refine ⟨⟨?_,ht0,ht1⟩,hkeep⟩
  intro j
  have hj : J-1-j.val<J := by omega
  have he : dst+(J-1-j.val)=dst+J-1-j.val := by omega
  rw [← he,hread _ hj,OutputDecodeOrder.indices_getD_reverse radix J (shiftTwo U c) j.isLt]
  simp only [rightRaw,one_mul,TernarySignedDigits.digit,TernarySignedDigits.quotient]
end Procs
end ThreeSum.LightTernarySignedRow
