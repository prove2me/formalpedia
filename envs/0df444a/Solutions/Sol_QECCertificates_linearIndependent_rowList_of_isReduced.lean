-- Prove2me | solution 1 for QECCertificates.linearIndependent_rowList_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:21.239406+00:00
-- url     : https://prove2.me/submissions/b5bf0541-9539-4fe3-8d50-d27fc8954c6f

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Theorems.Thm_QECCertificates_nodup_of_nodupPiv
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
open _root_.Matrix
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (hD : IsReduced D)
    (hnd : NodupPiv D) :
    LinearIndependent (ZMod 2) (fun i : Fin D.length => (D.get i).1) := by
  have hnod : D.Nodup := nodup_of_nodupPiv D hD hnd
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have h := congrFun hsum ((D.get i).2)
  rw [Finset.sum_apply] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  have hcongr : ∑ j ∈ s, g j * ((D.get j).1 ((D.get i).2))
      = ∑ j ∈ s, g j * (if j = i then (1 : ZMod 2) else 0) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hji : j = i
    · rw [hji, if_pos rfl, mul_one, hD.1 (D.get i) (List.get_mem D i), mul_one]
    · have hne : D.get j ≠ D.get i := fun hEq => hji (hnod.get_inj_iff.mp hEq)
      rw [if_neg hji, mul_zero,
        hD.2 (D.get j) (List.get_mem D j) (D.get i) (List.get_mem D i) hne, mul_zero]
  rw [hcongr] at h
  have hcollapse : ∑ j ∈ s, g j * (if j = i then (1 : ZMod 2) else 0) = g i := by
    have hh := Finset.sum_eq_single (s := s)
      (f := fun j => g j * (if j = i then (1 : ZMod 2) else 0)) i
      (fun b _ hne => by rw [if_neg (fun hc => hne hc), mul_zero])
      (fun hnot => absurd hi hnot)
    rwa [if_pos rfl, mul_one] at hh
  rw [hcollapse] at h
  exact h
end QECCertificates
