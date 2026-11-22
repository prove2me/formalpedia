-- Prove2me | solution 1 for QECCertificates.rowReduceFrom_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:44:05.497082+00:00
-- url     : https://prove2.me/submissions/c68a967a-2a9e-4c82-95fc-d441a4899a3a

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (D : List (PivRow n)) (v : Vec n) (rest : List (Vec n)) :
    rowReduceFrom D (v :: rest) = rowReduceFrom (step D v) rest := rfl
end QECCertificates
