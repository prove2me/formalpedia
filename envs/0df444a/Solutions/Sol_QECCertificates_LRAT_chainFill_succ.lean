-- Prove2me | solution 1 for QECCertificates.LRAT.chainFill_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:51:15.183328+00:00
-- url     : https://prove2.me/submissions/bef8f4f8-bcd5-4274-a08a-f438a661957a

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_chainFill_cons

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution (σ : Assign) (x : Nat) (rest : List Nat) (acc : Bool) (c t : Nat)
    (h : t ≠ c) :
    chainFill σ (x :: rest) acc c t = chainFill σ rest (acc ^^ σ x) (c + 1) t := by
  rw [chainFill_cons, if_neg h]
end QECCertificates.LRAT
