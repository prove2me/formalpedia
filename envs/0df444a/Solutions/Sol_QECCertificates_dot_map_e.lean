-- Prove2me | solution 1 for QECCertificates.dot_map_e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:54.651539+00:00
-- url     : https://prove2.me/submissions/1d4d870f-ebc7-4a73-8d38-fd86381fffe5

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basis
public import Theorems.Thm_QECCertificates_dotProduct_e_sum
public import Theorems.Thm_QECCertificates_sum_e_apply
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (A B : List (Fin n)) (hB : B.Nodup) :
    ((A.map e).sum) ⬝ᵥ ((B.map e).sum) = ((A.filter (fun a => a ∈ B)).length : ZMod 2) := by
  rw [dotProduct_e_sum]
  induction A with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.sum_cons, List.filter_cons, ih, sum_e_apply B hB a]
      by_cases ha : a ∈ B
      · simp [ha]
        ring
      · simp [ha]
end QECCertificates
