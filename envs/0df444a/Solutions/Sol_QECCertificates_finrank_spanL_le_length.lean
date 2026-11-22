-- Prove2me | solution 1 for QECCertificates.finrank_spanL_le_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:02.878443+00:00
-- url     : https://prove2.me/submissions/6a93bfee-e744-4327-ac3e-39b1ad61883f

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
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
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (A : List (Vec n)) :
    Module.finrank (ZMod 2) (spanL A) ≤ A.length := by
  have h : spanL A = Submodule.span (ZMod 2) (Set.range fun i : Fin A.length => A.get i) := by
    rw [spanL]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    exact List.mem_iff_get
  rw [h]
  calc Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range fun i : Fin A.length => A.get i))
      ≤ (Set.range (fun i : Fin A.length => A.get i)).toFinset.card := finrank_span_le_card _
    _ = Fintype.card ↑(Set.range fun i : Fin A.length => A.get i) := Set.toFinset_card _
    _ ≤ Fintype.card (Fin A.length) := Fintype.card_range_le _
    _ = A.length := Fintype.card_fin _
end QECCertificates
