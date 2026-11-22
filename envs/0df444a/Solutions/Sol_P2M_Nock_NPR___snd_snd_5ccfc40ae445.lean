-- Prove2me | solution 1 for P2M_Nock_NPR___snd_snd_5ccfc40ae445
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:00:03.402036+00:00
-- url     : https://prove2.me/submissions/9bc4ad12-a9e7-4aa2-a2c2-2a033f92da5b

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
theorem _root_.solution (n : Noun) : (Φ (K := K) n).2.2 = listPoly (dyckBits n) := rfl
end Nock.NPR
