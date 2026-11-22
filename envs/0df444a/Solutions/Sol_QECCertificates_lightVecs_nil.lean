-- Prove2me | solution 1 for QECCertificates.lightVecs_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:42:56.53006+00:00
-- url     : https://prove2.me/submissions/54c7cc02-d08e-4cae-bbcd-7ac8189d37c7

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (w : ℕ) : lightVecs 0 w = [0] := by rw [lightVecs.eq_1]
end QECCertificates
