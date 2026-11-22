-- Prove2me | solution 1 for QECCertificates.LRAT.chainFill_eq_false_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:44.76169+00:00
-- url     : https://prove2.me/submissions/51ed3c5b-b215-4aff-b164-ee81dab2c0e8

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_chainFill_succ

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution (σ : Assign) (rest : List Nat) (acc : Bool) (c : Nat) :
    ∀ t, t < c → chainFill σ rest acc c t = false := by
  induction rest generalizing acc c with
  | nil => intro t _; rfl
  | cons x rest ih =>
      intro t ht
      rw [chainFill_succ σ x rest acc c t (by omega)]
      exact ih (acc ^^ σ x) (c + 1) t (by omega)
end QECCertificates.LRAT
