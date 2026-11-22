-- Prove2me | solution 1 for QECCertificates.subset_spanL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:42:09.013705+00:00
-- url     : https://prove2.me/submissions/752a63df-6e7c-418e-bb23-e16515d93ff8

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
theorem _root_.solution {L : List (Vec n)} {x : Vec n} (h : x ∈ L) : x ∈ spanL L :=
  Submodule.subset_span h
end QECCertificates
