-- Prove2me | solution 1 for QECCertificates.sum_e_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:07.446918+00:00
-- url     : https://prove2.me/submissions/fd69451c-bf58-478e-8ef1-e56b39745ecf

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basis
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
theorem _root_.solution (l : List (Fin n)) (h : l.Nodup) (a : Fin n) :
    ((l.map e).sum : Vec n) a = if a ∈ l then 1 else 0 := by
  induction l with
  | nil => simp
  | cons b t ih =>
      obtain ⟨hb, ht⟩ := List.nodup_cons.mp h
      rw [List.map_cons, List.sum_cons, Pi.add_apply, ih ht]
      by_cases hab : a = b
      · subst hab; simp [hb, e, List.mem_cons]
      · have hzero : (e b) a = 0 := by simp [e, hab]
        rw [hzero, zero_add]
        simp [List.mem_cons, hab]
end QECCertificates
