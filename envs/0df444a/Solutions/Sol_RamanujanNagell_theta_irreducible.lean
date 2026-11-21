-- Prove2me | solution 1 for RamanujanNagell.theta_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:21.057426+00:00
-- url     : https://prove2.me/submissions/82024fc2-2602-4bbc-87ab-51d911da71ab

module
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_RamanujanNagell_Helpers
section
@[expose] public section
namespace RamanujanNagell
open QuadraticAlgebra
private lemma norm_factor_dichotomy {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hmn : m * n = 2) :
    m = 1 ∨ n = 1 := by
  have hm_pos : 0 < m := by rcases hm.lt_or_eq with h | h; exacts [h, by simp [← h] at hmn]
  have hn_pos : 0 < n := by rcases hn.lt_or_eq with h | h; exacts [h, by simp [← h] at hmn]
  have hm_le : m ≤ 2 := by nlinarith
  interval_cases m
  · left; rfl
  · right; linarith
private lemma isUnit_of_norm_one {a : R} (h : QuadraticAlgebra.norm a = 1) : IsUnit a := by
  apply QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
  rw [h]; exact isUnit_one
private lemma irreducible_of_norm_two {z : R} (hz : QuadraticAlgebra.norm z = 2) :
    Irreducible z := by
  refine ⟨?_, ?_⟩
  · intro hu
    have h2 : IsUnit (2 : ℤ) := hz ▸ QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hu
    exact absurd (Int.isUnit_iff.mp h2) (by decide)
  · intro a b hab
    have hnab : QuadraticAlgebra.norm a * QuadraticAlgebra.norm b = 2 := by
      rw [← map_mul, ← hab]; exact hz
    rcases norm_factor_dichotomy (norm_nonneg a) (norm_nonneg b) hnab with h | h
    · exact Or.inl (isUnit_of_norm_one h)
    · exact Or.inr (isUnit_of_norm_one h)
end RamanujanNagell
end
end

set_option autoImplicit true
@[expose] public section
public section
open RamanujanNagell
open QuadraticAlgebra
namespace RamanujanNagell
theorem _root_.solution : Irreducible θ := irreducible_of_norm_two rfl
end RamanujanNagell
