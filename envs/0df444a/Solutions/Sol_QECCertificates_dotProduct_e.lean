-- Prove2me | solution 1 for QECCertificates.dotProduct_e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:55.187107+00:00
-- url     : https://prove2.me/submissions/14c76c0a-b950-40d1-9e54-2453c60b3639

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basis
public import Theorems.Thm_QECCertificates_e_dotProduct

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (v : Vec n) (a : Fin n) : v ⬝ᵥ e a = v a := by
  rw [dotProduct_comm]; exact e_dotProduct a v
end QECCertificates
