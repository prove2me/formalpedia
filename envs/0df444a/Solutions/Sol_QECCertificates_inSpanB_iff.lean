-- Prove2me | solution 1 for QECCertificates.inSpanB_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:48.06145+00:00
-- url     : https://prove2.me/submissions/b03d58b1-2cd0-4d2c-83d3-7569f6b37dbb

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Theorems.Thm_QECCertificates_inSpanB_sound
public import Theorems.Thm_QECCertificates_inSpanB_complete

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (L : List (Vec n)) (v : Vec n) : inSpanB L v = true ↔ v ∈ spanL L :=
  ⟨inSpanB_sound, inSpanB_complete⟩
end QECCertificates
