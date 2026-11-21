-- Prove2me | solution 1 for P2M_RamanujanNagell_theta__not_dvd_theta_47b26ad22818
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:25.354352+00:00
-- url     : https://prove2.me/submissions/4cf01198-0e13-483c-9610-1f250591bc1e

module
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_RamanujanNagell_Helpers
public import Theorems.Thm_RamanujanNagell_theta_irreducible
public import Theorems.Thm_P2M_RamanujanNagell_theta__irreducible_a25aa7c76157
public import Theorems.Thm_P2M_RamanujanNagell_theta_theta__not_associated_fb452f5377b3

set_option autoImplicit true
@[expose] public section
public section
open RamanujanNagell
open QuadraticAlgebra
namespace RamanujanNagell
theorem _root_.solution : ¬ (θ' ∣ θ) := by
  intro h
  exact theta_theta'_not_associated
    (theta'_irreducible.associated_of_dvd theta_irreducible h).symm
end RamanujanNagell
