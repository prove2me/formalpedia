-- Prove2me | solution 1 for P2M_RamanujanNagell_theta_add_theta__c354e49fd50b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:21.75318+00:00
-- url     : https://prove2.me/submissions/b9d14859-0d7e-49fb-8c32-4a847036c5d0

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
theorem _root_.solution : θ + θ' = 1 := rfl
end RamanujanNagell
