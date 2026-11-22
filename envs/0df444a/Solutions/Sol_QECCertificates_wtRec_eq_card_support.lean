-- Prove2me | solution 1 for QECCertificates.wtRec_eq_card_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:24.725837+00:00
-- url     : https://prove2.me/submissions/d45b0841-a6c7-44df-9d73-6513fabd7d48

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
theorem _root_.solution (v : Vec n) : wtRec n v = (support v).card := by
  induction n with
  | zero => simp [wtRec, support]
  | succ n ih =>
      rw [wtRec_succ, ih]
      have hsupp : support v =
          (support (fun i : Fin n => v i.castSucc)).map Fin.castSuccEmb
            ∪ (if v (Fin.last n) = 0 then ∅ else {Fin.last n}) := by
        ext i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | hj
        · rw [hj, mem_support]
          by_cases hb : v (Fin.last n) = 0 <;>
            simp [support, castSuccEmb_apply, hb, Fin.castSucc_inj, Fin.castSucc_ne_last]
        · rw [hj, mem_support]
          by_cases hb : v (Fin.last n) = 0 <;>
            simp [support, castSuccEmb_apply, hb, Fin.castSucc_ne_last]
      rw [hsupp, Finset.card_union_of_disjoint, Finset.card_map]
      · by_cases hb : v (Fin.last n) = 0 <;> simp [hb]
      · rw [Finset.disjoint_left]
        intro a ha hb
        rw [Finset.mem_map] at ha
        obtain ⟨j, _, hj⟩ := ha
        rw [← hj] at hb
        by_cases h0 : v (Fin.last n) = 0
        · simp [h0] at hb
        · simp only [h0, ite_false, Finset.mem_singleton] at hb
          exact Fin.castSucc_ne_last j hb
end QECCertificates
