-- Prove2me | solution 1 for QECCertificates.not_mem_rowSpace_of_inSpanB_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:58.147061+00:00
-- url     : https://prove2.me/submissions/d69a71f5-3df3-45d2-a1a2-c43bd583a386

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Definitions.Def_LeanPool_QECCertificates_GF2_LowerBound
public import Theorems.Thm_QECCertificates_Matrix_rowSpace_eq_spanL_ofFn
public import Theorems.Thm_QECCertificates_inSpanB_eq_false_iff


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2))
    {v : Vec n} (h : inSpanB (List.ofFn fun i => M i) v = false) : v ∉ M.certificateRowSpace := by
  rw [Matrix.rowSpace_eq_spanL_ofFn]
  exact (inSpanB_eq_false_iff _ v).mp h
end QECCertificates
