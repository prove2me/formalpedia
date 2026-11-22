-- Prove2me | solution 1 for QECCertificates.Matrix.rank_eq_length_rowReduce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:50.646277+00:00
-- url     : https://prove2.me/submissions/787b4b41-99d2-41e9-8d00-b286105547e9

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Theorems.Thm_QECCertificates_finrank_spanL_eq_length_rowReduce
public import Theorems.Thm_QECCertificates_Matrix_rank_eq_finrank_rowSpace
public import Theorems.Thm_QECCertificates_Matrix_rowSpace_eq_spanL_ofFn


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
open _root_.Matrix
variable {n : ℕ}
namespace QECCertificates
namespace Matrix
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    M.rank = (rowReduce (List.ofFn fun i => M i)).length := by
  rw [Matrix.rank_eq_finrank_rowSpace, Matrix.rowSpace_eq_spanL_ofFn]
  exact finrank_spanL_eq_length_rowReduce _
end Matrix
end QECCertificates
