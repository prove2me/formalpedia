-- Prove2me | solution 1 for QECCertificates.Matrix.rowSpace_eq_spanL_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:43:20.736489+00:00
-- url     : https://prove2.me/submissions/b074508c-07d4-45ab-ac4a-7eca537e5f33

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_add_self
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.add_self

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
namespace Matrix
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    M.certificateRowSpace = spanL (List.ofFn fun i => M i) := by
  change Submodule.span (ZMod 2) (Set.range fun i => M i) = spanL (List.ofFn fun i => M i)
  rw [spanL]
  congr 1
  ext x
  change x ∈ Set.range (fun i => M i) ↔ x ∈ List.ofFn (fun i => M i)
  rw [List.mem_ofFn, Set.mem_range]
end Matrix
end QECCertificates
