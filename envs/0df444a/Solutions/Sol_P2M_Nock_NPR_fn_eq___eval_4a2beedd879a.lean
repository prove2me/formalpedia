-- Prove2me | solution 1 for P2M_Nock_NPR_fn_eq___eval_4a2beedd879a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:54.027847+00:00
-- url     : https://prove2.me/submissions/f61ea4d8-ca00-4bbf-8c0c-cc8036e69988

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_listPoly_nil
public import Theorems.Thm_Nock_NPR_leafF_length
attribute [local simp] Nock.NPR.listPoly_nil
attribute [local simp] Nock.NPR.leafF_length

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]
namespace Nock.NPR
theorem _root_.solution (n : Noun) (r : K) :
    fn n r = ((Φ n).1.eval r, (Φ (K := K) n).2.1.eval r, (Φ n).2.2.eval r) := by
  simp [fn, Φ]
end Nock.NPR
