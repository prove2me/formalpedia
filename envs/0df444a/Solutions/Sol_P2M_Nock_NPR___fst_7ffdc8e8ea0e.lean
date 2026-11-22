-- Prove2me | solution 1 for P2M_Nock_NPR___fst_7ffdc8e8ea0e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:00:06.133664+00:00
-- url     : https://prove2.me/submissions/23a21c06-01a2-4650-8157-73412618613f

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]
namespace Nock.NPR
theorem _root_.solution (n : Noun) : (Φ (K := K) n).1 = X ^ n.leaves := rfl
end Nock.NPR
