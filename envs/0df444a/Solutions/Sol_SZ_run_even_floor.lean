-- Prove2me | solution 1 for SZ.run_even_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:19:33.316971+00:00
-- url     : https://prove2.me/submissions/637df5e4-d9cf-44e2-8121-51e4f66fb4f5

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_isDigits_run_fst
import Theorems.Thm_SZ_isDigits_runY
import Theorems.Thm_SZ_run_coupling
import Theorems.Thm_SZ_even_floor_add_digitReal_mul_pow


set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {d : ℕ → ℤ × ℤ} (hrun : IsRun (-12, 9) d)
    (hA : ∀ N, ∃ k, N ≤ k ∧ (d k).1 = 0) (hB : ∀ N, ∃ k, N ≤ k ∧ (d k).2 = 2)
    {n : ℕ} (hn : 1 ≤ n) : Even ⌊runXi d * Real.sqrt 3 ^ n⌋ := by
  have heven : ∀ i, Even (d i).1 := fun i => by
    rcases (hrun i).1.1 with h | h <;> rw [h] <;> decide
  have hevenY : ∀ i, Even (runY d i) := fun i => by
    rcases (hrun i).1.2 with h | h <;> simp only [runY, h] <;> decide
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨t, ht⟩ := he
    obtain ⟨s, rfl⟩ : ∃ s, n = 2 * (s + 1) := ⟨t - 1, by omega⟩
    obtain ⟨i₀, hi₀, hz⟩ := hA s
    have hval : runXi d * Real.sqrt 3 ^ (2 * (s + 1))
        = (((4 : ℤ) : ℝ) + digitReal 3 (fun i => (d i).1)) * ((3 : ℕ) : ℝ) ^ s := by
      rw [pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), runXi]
      push_cast
      rw [pow_succ]
      ring
    rw [hval]
    exact even_floor_add_digitReal_mul_pow (isDigits_run_fst hrun) (by decide) heven s hi₀
      (show (d i₀).1 ≤ ((3 : ℕ) : ℤ) - 2 by rw [hz]; norm_num)
  · obtain ⟨s, rfl⟩ := ho
    obtain ⟨i₀, hi₀, hz⟩ := hB s
    have hsmall : runY d i₀ ≤ ((3 : ℕ) : ℤ) - 2 := by simp [runY, hz]
    have hval : runXi d * Real.sqrt 3 ^ (2 * s + 1)
        = (((2 : ℤ) : ℝ) + digitReal 3 (runY d)) * ((3 : ℕ) : ℝ) ^ s := by
      rw [pow_succ, pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), runXi,
        show (4 : ℝ) + digitReal 3 (fun i => (d i).1)
          = Real.sqrt 3 * (2 + digitReal 3 (runY d)) from run_coupling hrun]
      push_cast
      field_simp
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
      ring
    rw [hval]
    exact even_floor_add_digitReal_mul_pow (isDigits_runY hrun) (by decide) hevenY s hi₀ hsmall
end SZ
