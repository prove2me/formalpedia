-- Prove2me | solution 1 for RamanujanNagell.theta_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:57.915027+00:00
-- url     : https://prove2.me/submissions/a1af77b8-bca5-48f0-a58a-021636bdda32

module
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_RamanujanNagell_Helpers
public import Theorems.Thm_RamanujanNagell_theta_irreducible

set_option autoImplicit true
@[expose] public section
public section
open RamanujanNagell
open QuadraticAlgebra
namespace RamanujanNagell
theorem _root_.solution : Prime θ :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp theta_irreducible
end RamanujanNagell
