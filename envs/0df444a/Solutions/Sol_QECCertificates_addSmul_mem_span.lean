-- Prove2me | solution 1 for QECCertificates.addSmul_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:01.834876+00:00
-- url     : https://prove2.me/submissions/8204ca55-7e1b-403c-9cb3-1ebb6a497922

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
theorem _root_.solution {S : Set (Vec n)} {v r : Vec n} (c : ZMod 2)
    (hv : v ∈ Submodule.span (ZMod 2) S) (hr : r ∈ Submodule.span (ZMod 2) S) :
    addSmul v r c ∈ Submodule.span (ZMod 2) S :=
  Submodule.add_mem _ hv (Submodule.smul_mem _ c hr)
end QECCertificates
