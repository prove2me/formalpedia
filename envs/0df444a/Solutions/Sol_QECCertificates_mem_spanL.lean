-- Prove2me | solution 1 for QECCertificates.mem_spanL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:32.70585+00:00
-- url     : https://prove2.me/submissions/42240668-dc32-4926-9c8e-20daac0a1cba

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {L : List (Vec n)} {x : Vec n} :
    x ∈ spanL L ↔ x ∈ Submodule.span (ZMod 2) {y | y ∈ L} := Iff.rfl
end QECCertificates
