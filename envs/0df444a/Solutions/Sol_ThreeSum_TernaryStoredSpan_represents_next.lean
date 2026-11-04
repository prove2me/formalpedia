-- Prove2me | solution 1 for ThreeSum.TernaryStoredSpan.represents_next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:17:28.098735+00:00
-- url     : https://prove2.me/submissions/dbb48274-1431-4467-8bf8-92caf53c8d52

import Definitions.Def_Submission_ThreeSum_LightSpanCatalogTest
import Definitions.Def_Submission_ThreeSum_TernaryStoredSpan
import Theorems.Thm_ThreeSum_TernaryStoredSpan_next_at
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryStoredSpan
open ThreeSum
set_option maxHeartbeats 3000000
variable {p J n : ℕ}
namespace ThreeSum.TernaryStoredSpan
theorem _root_.solution [Fact p.Prime] (f : ℕ → ℕ → ℕ) (row : Fin J → ZMod p)
    (rows : List (Fin J → ZMod p)) (hn : 0<n) (H : Represents f n rows) :
    Represents (next f (fun i => if hi : i<J then (row ⟨i,hi⟩).val else 0) p n) (p*n) (row::rows) := by
  intro w
  have hs : {v | v∈row::rows}=insert row {v | v∈rows} := by
    ext v
    simp only [Set.mem_setOf_eq,Set.mem_insert_iff,List.mem_cons]
  rw [hs]
  constructor
  · intro hw
    obtain ⟨a,v,hv,he⟩ := (Submodule.mem_span_insert (R := ZMod p) (x := w) (y := row)
      (s := {v | v∈rows})).mp hw
    obtain ⟨k,hk,hvrep⟩ := (H v).mp hv
    have ha := ZMod.val_lt a
    refine ⟨a.val*n+k,?_,?_⟩
    · have hb := Nat.mul_le_mul_right n (show a.val+1≤p by omega)
      nlinarith
    · intro i
      rw [next_at _ _ hn hk i.val]
      simp only [dif_pos i.isLt,ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val]
      rw [hvrep i]
      have hi := congrArg (fun v : Fin J → ZMod p => v i) he
      simpa [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_comm] using hi.symm
  · rintro ⟨q,hq,hrep⟩
    let k := q%n
    let a : ZMod p := (q/n : ℕ)
    let v : Fin J → ZMod p := fun i => (f k i.val : ZMod p)
    have hk : k<n := Nat.mod_lt _ hn
    have hv : v∈Submodule.span (ZMod p) {v | v∈rows} := (H v).mpr ⟨k,hk,fun _ => rfl⟩
    have hw : w=a • row+v := by
      funext i
      have hh := hrep i
      simp only [next,dif_pos i.isLt,ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val] at hh
      simpa [a,v,k,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_comm] using hh.symm
    exact (Submodule.mem_span_insert (R := ZMod p) (x := w) (y := row)
      (s := {v | v∈rows})).mpr ⟨a,v,hv,hw⟩
end ThreeSum.TernaryStoredSpan
