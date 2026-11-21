-- Prove2me | solution 1 for RamanujanNagell.two_factorisation_R
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:18.999891+00:00
-- url     : https://prove2.me/submissions/6248684e-53ec-4cb4-803f-da7c8e1796f4

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
theorem _root_.solution : θ * (1 - θ) = 2 := rfl
end RamanujanNagell
