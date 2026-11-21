-- Prove2me | solution 1 for P2M_RamanujanNagell_theta__prime_6708f1803f40
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:54.9329+00:00
-- url     : https://prove2.me/submissions/70ae7074-4b67-486e-a5f3-72a7b7794ac8

module
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_RamanujanNagell_Helpers
public import Theorems.Thm_P2M_RamanujanNagell_theta__irreducible_a25aa7c76157

set_option autoImplicit true
@[expose] public section
public section
open RamanujanNagell
open QuadraticAlgebra
namespace RamanujanNagell
theorem _root_.solution : Prime θ' :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp theta'_irreducible
end RamanujanNagell
