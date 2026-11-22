-- Prove2me | solution 1 for QECCertificates.col_decomp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:48.494458+00:00
-- url     : https://prove2.me/submissions/158cc743-978a-4722-99b9-ab7190143d97

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Theorems.Thm_QECCertificates_isReduced_rowReduce
public import Theorems.Thm_QECCertificates_readOff_apply
public import Theorems.Thm_QECCertificates_readOff_eq_of_mem_spanL
public import Theorems.Thm_QECCertificates_spanL_rowReduce


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) (c : List (Vec m))
    (hc : ∀ j : Fin k, (fun i => M i j) ∈ spanL c) (i : Fin m) (j : Fin k) :
    M i j = ∑ ri ∈ (rowReduce c).toFinset, (M ri.2 j) * (ri.1 i) := by
  have hmem : (fun i => M i j) ∈ spanL (rowList (rowReduce c)) := by
    rw [spanL_rowReduce]
    exact hc j
  have h := congrFun (readOff_eq_of_mem_spanL (isReduced_rowReduce c) hmem) i
  rw [readOff_apply] at h
  exact h.symm
end QECCertificates
