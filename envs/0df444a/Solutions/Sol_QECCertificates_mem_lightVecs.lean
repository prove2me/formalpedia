-- Prove2me | solution 1 for QECCertificates.mem_lightVecs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:58:24.934569+00:00
-- url     : https://prove2.me/submissions/fefc2452-20ad-4fd7-916f-0c1d69c32f48

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Theorems.Thm_QECCertificates_snocV_castSucc
public import Theorems.Thm_QECCertificates_castSuccEmb_apply
public import Theorems.Thm_QECCertificates_snocV_last
public import Theorems.Thm_QECCertificates_snocV_zero_zero
public import Theorems.Thm_QECCertificates_snocV_prefix_last
public import Theorems.Thm_QECCertificates_wtRec_zero
public import Theorems.Thm_QECCertificates_wtRec_succ
public import Theorems.Thm_QECCertificates_lightVecs_nil
public import Theorems.Thm_QECCertificates_lightVecs_zero
public import Theorems.Thm_QECCertificates_lightVecs_succ_succ
public import Theorems.Thm_QECCertificates_wtRec_eq_zero_iff
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_eq_one_of_ne_zero
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
theorem _root_.solution : ∀ (n w : ℕ) (v : Vec n), wtRec n v ≤ w → v ∈ lightVecs n w := by
  intro n
  induction n with
  | zero =>
      intro w v _
      rw [lightVecs_nil]
      simp only [List.mem_singleton]
      funext i
      exact i.elim0
  | succ n ih =>
      intro w v hv
      cases w with
      | zero =>
          have hv0 : v = 0 := (wtRec_eq_zero_iff v).mp (Nat.le_zero.mp hv)
          rw [hv0, lightVecs_zero]; simp
      | succ w =>
          rw [← snocV_prefix_last v, lightVecs_succ_succ]
          rw [wtRec_succ] at hv
          by_cases hb : v (Fin.last n) = 0
          · rw [hb] at hv ⊢
            rw [if_pos rfl] at hv
            refine List.mem_append_left _ ?_
            rw [List.mem_map]
            exact ⟨fun i : Fin n => v i.castSucc, ih (w + 1) _ hv, rfl⟩
          · rw [if_neg hb] at hv
            have hb1 : v (Fin.last n) = 1 := eq_one_of_ne_zero hb
            rw [hb1]
            refine List.mem_append_right _ ?_
            rw [List.mem_map]
            exact ⟨fun i : Fin n => v i.castSucc, ih w _ (by omega), rfl⟩
end QECCertificates
