-- Prove2me | solution 1 for QECCertificates.kerVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:48:25.793128+00:00
-- url     : https://prove2.me/submissions/a323c778-f794-4339-b1ac-c2342fe6b4ca

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
theorem _root_.solution (D : List (PivRow n)) (j i : Fin n) :
    kerVec D j i
      = (if i = j then 1 else 0) + ∑ ri ∈ D.toFinset, (if ri.2 = i then ri.1 j else 0) := rfl
end QECCertificates
