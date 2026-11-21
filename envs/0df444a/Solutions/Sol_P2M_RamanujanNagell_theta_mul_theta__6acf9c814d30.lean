-- Prove2me | solution 1 for P2M_RamanujanNagell_theta_mul_theta__6acf9c814d30
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:17.395843+00:00
-- url     : https://prove2.me/submissions/32edab72-ecfe-4865-822d-2fd1f4787675

module
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_RamanujanNagell_Helpers

set_option autoImplicit true
@[expose] public section
public section
open RamanujanNagell
open QuadraticAlgebra
namespace RamanujanNagell
theorem _root_.solution : θ * θ' = 2 := rfl
end RamanujanNagell
