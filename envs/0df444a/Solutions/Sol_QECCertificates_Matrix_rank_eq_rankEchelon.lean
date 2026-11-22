-- Prove2me | solution 1 for QECCertificates.Matrix.rank_eq_rankEchelon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:12.971699+00:00
-- url     : https://prove2.me/submissions/09af3540-51b2-430b-bd19-78bd1e1b2554

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_rankEchelon_eq_length_rowReduce
public import Theorems.Thm_QECCertificates_Matrix_rank_eq_length_rowReduce


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
namespace Matrix
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    M.rank = rankEchelon (List.ofFn fun i => M i) := by
  rw [Matrix.rank_eq_length_rowReduce, rankEchelon_eq_length_rowReduce]
end Matrix
end QECCertificates
