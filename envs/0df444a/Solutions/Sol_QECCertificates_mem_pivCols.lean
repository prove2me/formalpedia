-- Prove2me | solution 1 for QECCertificates.mem_pivCols
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:45:31.730021+00:00
-- url     : https://prove2.me/submissions/df8ef819-2b4b-4ea5-b50d-d354c9b1c6c6

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} {i : Fin n} :
    i ∈ pivCols D ↔ ∃ ri ∈ D, ri.2 = i := by
  rw [pivCols, List.mem_toFinset, List.mem_map]
end QECCertificates
