-- Prove2me | solution 1 for P2M_Nock_NPR___snd_fst_ac932a0e2667
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:00:02.939368+00:00
-- url     : https://prove2.me/submissions/5d19aa21-d0b1-4461-9066-ed098bfc8ca2

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
theorem _root_.solution (n : Noun) : (Φ (K := K) n).2.1 = listPoly (leafF n) := rfl
end Nock.NPR
