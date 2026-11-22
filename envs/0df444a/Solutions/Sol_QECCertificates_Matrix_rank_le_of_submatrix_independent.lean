-- Prove2me | solution 1 for QECCertificates.Matrix.rank_le_of_submatrix_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:28.721239+00:00
-- url     : https://prove2.me/submissions/0fada826-3625-4b3f-bb3a-2d3660a46823

module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
namespace QECCertificates
namespace Matrix
theorem _root_.solution
  {k r n : ℕ}
  (M : Matrix (Fin r) (Fin n) (ZMod 2))
  (inds : Fin k → Fin r)
  (_inds_mono : StrictMono inds)
  (h_ind : LinearIndependent (ZMod 2) (M.submatrix inds id)) :
  k ≤ M.rank := by
    have hrow : LinearIndependent (ZMod 2) ((M.submatrix inds id).row) := by
      simpa only [Matrix.row] using h_ind
    have h_submatrix_rank : (M.submatrix inds id).rank = k := by
      simpa using LinearIndependent.rank_matrix hrow
    calc k = (M.submatrix inds id).rank := h_submatrix_rank.symm
      _ ≤ M.rank := Matrix.rank_submatrix_le M inds id
end Matrix
end QECCertificates
