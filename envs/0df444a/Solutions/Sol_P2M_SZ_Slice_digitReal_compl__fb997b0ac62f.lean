-- Prove2me | solution 1 for P2M_SZ_Slice_digitReal_compl__fb997b0ac62f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:26:10.503488+00:00
-- url     : https://prove2.me/submissions/c5f8cebd-cfee-452c-9a3b-57b20011282c

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_three_le_cast
import Theorems.Thm_P2M_SZ_IsDigits_pow_pos__7f25d03f067c
import Theorems.Thm_SZ_IsDigits_cast_pos
import Theorems.Thm_SZ_IsDigits_one_lt_cast
import Theorems.Thm_SZ_digitSum_succ
import Theorems.Thm_SZ_digitSum_tendsto


set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
variable {S}
namespace SZ.Slice
theorem _root_.solution (S : Slice) {d : ℕ → ℤ} (h : IsDigits S.m d) (hd : ∀ i, d i ≤ S.e) :
    digitReal S.m (fun i => S.e - d i) = S.M - digitReal S.m d := by
  have hm1 : (0 : ℝ) < (S.m : ℝ) - 1 := by have := S.three_le_cast; linarith
  have hc : IsDigits S.m (fun i => S.e - d i) :=
    { two_le := h.two_le
      nonneg := fun i => by have := hd i; omega
      le_sub_one := fun i => by have := h.nonneg i; have := S.e_le; omega }
  have hpartial : ∀ k, digitSum S.m (fun i => S.e - d i) k
      = S.M * (1 - 1 / (S.m : ℝ) ^ k) - digitSum S.m d k := by
    intro k
    induction k with
    | zero => simp [digitSum]
    | succ k ih =>
      rw [digitSum_succ, digitSum_succ, ih, M]
      have hp : (0 : ℝ) < (S.m : ℝ) ^ k := h.pow_pos' _
      have hp1 : (0 : ℝ) < (S.m : ℝ) ^ (k + 1) := h.pow_pos' _
      push_cast
      field_simp
      ring
  have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / (S.m : ℝ) ^ k) atTop (𝓝 0) := by
    have hpow : ∀ k : ℕ, (1 : ℝ) / (S.m : ℝ) ^ k = (1 / (S.m : ℝ)) ^ k := fun k => by
      rw [div_pow, one_pow]
    simp only [hpow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      ((div_lt_one h.cast_pos).mpr h.one_lt_cast)
  have hlim : Tendsto (digitSum S.m (fun i => S.e - d i)) atTop (𝓝 (S.M - digitReal S.m d)) := by
    have hfun : digitSum S.m (fun i => S.e - d i)
        = fun k => S.M * (1 - 1 / (S.m : ℝ) ^ k) - digitSum S.m d k := funext hpartial
    rw [hfun]
    have hone : S.M - digitReal S.m d = S.M * (1 - 0) - digitReal S.m d := by ring
    rw [hone]
    exact ((tendsto_const_nhds (x := S.M)).mul
      ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub h0)).sub (digitSum_tendsto h)
  exact tendsto_nhds_unique (digitSum_tendsto hc) hlim
end SZ.Slice
