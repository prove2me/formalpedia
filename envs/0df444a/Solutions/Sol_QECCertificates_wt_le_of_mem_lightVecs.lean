-- Prove2me | solution 1 for QECCertificates.wt_le_of_mem_lightVecs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:32.921821+00:00
-- url     : https://prove2.me/submissions/fc0d8b72-eaf6-42e1-afe8-0c322e6d4c67

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Theorems.Thm_QECCertificates_snocV_castSucc
public import Theorems.Thm_QECCertificates_castSuccEmb_apply
public import Theorems.Thm_QECCertificates_snocV_last
public import Theorems.Thm_QECCertificates_snocV_zero_zero
public import Theorems.Thm_QECCertificates_wtRec_zero
public import Theorems.Thm_QECCertificates_wtRec_succ
public import Theorems.Thm_QECCertificates_lightVecs_nil
public import Theorems.Thm_QECCertificates_lightVecs_zero
public import Theorems.Thm_QECCertificates_lightVecs_succ_succ
public import Theorems.Thm_QECCertificates_wtRec_eq_zero_iff
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support


attribute [local simp] QECCertificates.snocV_castSucc
attribute [local simp] QECCertificates.castSuccEmb_apply
attribute [local simp] QECCertificates.snocV_last
attribute [local simp] QECCertificates.snocV_zero_zero
attribute [local simp] QECCertificates.wtRec_zero
attribute [local simp] QECCertificates.lightVecs_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution : ∀ (n w : ℕ) (v : Vec n), v ∈ lightVecs n w → wtRec n v ≤ w := by
  intro n
  induction n with
  | zero =>
      intro w v hv
      rw [lightVecs_nil, List.mem_singleton] at hv
      subst hv
      have h0 : wtRec 0 (0 : Vec 0) = 0 := wtRec_zero 0
      rw [h0]
      omega
  | succ n ih =>
      intro w v hv
      cases w with
      | zero =>
          rw [lightVecs_zero, List.mem_singleton] at hv
          subst hv
          have h0 : wtRec (n + 1) (0 : Vec (n + 1)) = 0 :=
            (wtRec_eq_zero_iff (0 : Vec (n + 1))).mpr rfl
          rw [h0]
      | succ w =>
          rw [lightVecs_succ_succ, List.mem_append] at hv
          rcases hv with hv | hv
          · rw [List.mem_map] at hv
            obtain ⟨u, hu, huv⟩ := hv
            subst huv
            have h := ih (w + 1) u hu
            have heq : wtRec (n + 1) (snocV u 0) = wtRec n u := by
              rw [wtRec_succ, snocV_last]
              simp
            rw [heq]
            omega
          · rw [List.mem_map] at hv
            obtain ⟨u, hu, huv⟩ := hv
            subst huv
            have h := ih w u hu
            have heq : wtRec (n + 1) (snocV u 1) = wtRec n u + 1 := by
              rw [wtRec_succ, snocV_last]
              simp
            rw [heq]
            omega
end QECCertificates
