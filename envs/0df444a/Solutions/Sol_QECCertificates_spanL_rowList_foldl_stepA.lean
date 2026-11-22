-- Prove2me | solution 1 for QECCertificates.spanL_rowList_foldl_stepA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:27.494065+00:00
-- url     : https://prove2.me/submissions/c8f501a4-8b2a-4f2e-8dd3-fa09f0a5917c

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_spanL_rowList_stepA
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
public import Theorems.Thm_QECCertificates_spanL_append
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
theorem _root_.solution (D : List (PivRow n)) (L : List (Vec n)) :
    spanL (rowList (L.foldl stepA D)) = spanL (rowList D ++ L) := by
  induction L generalizing D with
  | nil => simp
  | cons v rest ih =>
      rw [List.foldl_cons, ih (stepA D v)]
      calc spanL (rowList (stepA D v) ++ rest)
          = spanL (rowList (stepA D v)) ⊔ spanL rest := spanL_append _ _
        _ = spanL (rowList D ++ [v]) ⊔ spanL rest := by rw [spanL_rowList_stepA]
        _ = (spanL (rowList D) ⊔ spanL [v]) ⊔ spanL rest := by rw [spanL_append]
        _ = spanL (rowList D) ⊔ (spanL [v] ⊔ spanL rest) := sup_assoc _ _ _
        _ = spanL (rowList D) ⊔ spanL ([v] ++ rest) := by rw [spanL_append]
        _ = spanL (rowList D ++ (v :: rest)) := (spanL_append _ _).symm
end QECCertificates
