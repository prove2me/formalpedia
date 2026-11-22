-- Prove2me | solution 1 for QECCertificates.wtRec_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:57:47.109319+00:00
-- url     : https://prove2.me/submissions/22d27a4e-2769-40ea-82c0-26cfb0c0c181

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
theorem _root_.solution (v : Vec n) : wtRec n v = 0 ↔ v = 0 := by
  induction n with
  | zero =>
      refine ⟨fun _ => ?_, fun _ => by simp⟩
      funext i
      exact i.elim0
  | succ n ih =>
      rw [wtRec_succ]
      constructor
      · intro h
        have hb : v (Fin.last n) = 0 := by
          by_contra hb
          rw [if_neg hb] at h
          omega
        rw [if_pos hb, add_zero] at h
        have hpre : (fun i : Fin n => v i.castSucc) = 0 := (ih _).mp h
        rw [← snocV_prefix_last v, hb, hpre, snocV_zero_zero]
      · intro h
        rw [h]
        simp only [Pi.zero_apply, ite_true, add_zero]
        exact (ih 0).mpr rfl
end QECCertificates
