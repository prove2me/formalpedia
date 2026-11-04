-- Prove2me | solution 1 for ThreeSum.TernaryStoredSpan.read_next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:13:16.865092+00:00
-- url     : https://prove2.me/submissions/e83b6225-5139-42e6-bb52-57b85645cace

import Definitions.Def_Submission_ThreeSum_LightSpanCatalogTest
import Definitions.Def_Submission_ThreeSum_TernaryStoredSpan
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
theorem _root_.solution {μ : ℕ → ℤ} {src J p n : ℕ} (f : ℕ → ℕ → ℕ) (row : ℕ → ℕ) (hn : 0<n)
    (H : ∀ a<p, ∀ k<n, ∀ i<J, μ (src+J*n*a+J*k+i)=LightSpanAxpy.values (f k) row a p i) :
    ∀ q<p*n, ∀ i<J, μ (src+J*q+i)=(next f row p n q i : ℤ) := by
  intro q hq i hi
  have ha : q/n<p := (Nat.div_lt_iff_lt_mul hn).mpr (by simpa only [Nat.mul_comm] using hq)
  have hk : q%n<n := Nat.mod_lt _ hn
  have hh := H (q/n) ha (q%n) hk i hi
  have he : J*q=J*n*(q/n)+J*(q%n) := by
    have hz := Nat.div_add_mod q n
    calc
      J*q=J*(n*(q/n)+q%n) := congrArg (fun x => J*x) hz.symm
      _=_ := by ring
  simpa only [he,LightSpanAxpy.values,next,Nat.add_assoc] using hh
end ThreeSum.TernaryStoredSpan
