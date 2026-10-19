-- Prove2me | solution 1 for PermanentRollout.affine_le_of_shifted_choose_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/8db878f0-774a-485f-b86c-252eba18c26e

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_affine_tendsto_shifted_choose_ratio

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    (L P n M₀ : ℕ)
    (hbound : ∀ m : ℕ,
      L * (m + n).choose n ≤
        P * (m + M₀ + n).choose n) :
    L ≤ P := by
  have hratio := affine_tendsto_shifted_choose_ratio n M₀
  have hlim :
      Tendsto
        (fun m : ℕ =>
          (P : ℝ) *
            (((m + M₀ + n).choose n : ℝ) /
              ((m + n).choose n : ℝ)))
        atTop (𝓝 (P : ℝ)) := by
    simpa using tendsto_const_nhds.mul hratio
  have hle : ∀ m : ℕ,
      (L : ℝ) ≤
        (P : ℝ) *
          (((m + M₀ + n).choose n : ℝ) /
            ((m + n).choose n : ℝ)) := by
    intro m
    have hpos : (0 : ℝ) < ((m + n).choose n : ℝ) := by
      exact_mod_cast Nat.choose_pos (show n ≤ m + n by omega)
    have hb :
        (L : ℝ) * ((m + n).choose n : ℝ) ≤
          (P : ℝ) * ((m + M₀ + n).choose n : ℝ) := by
      exact_mod_cast hbound m
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hpos).2 hb
  have hreal : (L : ℝ) ≤ (P : ℝ) :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hle
  exact_mod_cast hreal
end PermanentRollout
