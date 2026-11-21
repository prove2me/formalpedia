-- Prove2me | solution 1 for P2M_RamanujanNagell_theta_not_dvd_theta__caa5edc7b0d5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:24.763238+00:00
-- url     : https://prove2.me/submissions/d137f5cc-efdc-44cf-84cb-352393c2a075

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
theorem _root_.solution : ¬ (θ ∣ θ') := by
  intro h
  exact theta_theta'_not_associated (theta_irreducible.associated_of_dvd theta'_irreducible h)
end RamanujanNagell
