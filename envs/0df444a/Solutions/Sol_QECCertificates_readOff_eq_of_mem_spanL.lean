-- Prove2me | solution 1 for QECCertificates.readOff_eq_of_mem_spanL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:58.64864+00:00
-- url     : https://prove2.me/submissions/aa49f0b4-c8e6-44be-9167-d1092c56f142

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Theorems.Thm_QECCertificates_readOff_nil
public import Theorems.Thm_QECCertificates_readOff_add
public import Theorems.Thm_QECCertificates_readOff_smul
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


attribute [local simp] QECCertificates.readOff_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (hD : IsReduced D) {w : Vec n}
    (hw : w ∈ spanL (rowList D)) : readOff D w = w := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · intro x hx
    obtain ⟨ri, hri, hri1⟩ := List.mem_map.mp hx
    rw [← hri1]
    simp only [readOff]
    refine (Finset.sum_eq_single (s := D.toFinset)
      (f := fun rj : PivRow n => (ri.1 rj.2) • rj.1) ri ?_ ?_).trans ?_
    · intro rj hrj hne
      rw [hD.2 ri hri rj (List.mem_toFinset.mp hrj) hne.symm, zero_smul]
    · intro hnot
      exact absurd (List.mem_toFinset.mpr hri) hnot
    · rw [hD.1 ri hri, one_smul]
  · simp only [readOff]
    refine Finset.sum_eq_zero fun ri _ => ?_
    rw [Pi.zero_apply, zero_smul]
  · intro x y _ _ hx hy
    rw [readOff_add, hx, hy]
  · intro c x _ hx
    rw [readOff_smul, hx]
end QECCertificates
