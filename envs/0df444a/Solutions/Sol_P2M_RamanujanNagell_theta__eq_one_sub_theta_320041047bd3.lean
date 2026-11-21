-- Prove2me | solution 1 for P2M_RamanujanNagell_theta__eq_one_sub_theta_320041047bd3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:18.291361+00:00
-- url     : https://prove2.me/submissions/cee5b5ee-ea9e-4990-a3db-97ecad146c2a

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
theorem _root_.solution : θ' = 1 - θ := rfl
end RamanujanNagell
