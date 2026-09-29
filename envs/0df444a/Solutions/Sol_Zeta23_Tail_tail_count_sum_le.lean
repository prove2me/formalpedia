-- Prove2me | solution 1 for Zeta23.Tail.tail_count_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:00:14.741415+00:00
-- url     : https://prove2.me/submissions/98988f4a-413e-41ac-86b2-8af97b2f0960

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Zeta23_Tail_Basic
import Theorems.Thm_Zeta23_Tail_one_side_sum_le
import Theorems.Thm_Zeta23_Tail_two_sides_numeric

-- from Zeta23.Tail.Basic
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/Basic.lean — shared elementary definitions for prop:tail (the paper §4.2).
-/

noncomputable section

namespace Zeta23
namespace Tail



lemma distI_of_le {T γ : ℝ} (hT : 0 ≤ T) (h : γ ≤ T) : distI T γ = T - γ := by
  unfold distI
  have h1 : max (T - γ) (γ - 2 * T) = T - γ := max_eq_left (by linarith)
  rw [h1, max_eq_right (by linarith)]

lemma distI_of_ge {T γ : ℝ} (hT : 0 ≤ T) (h : 2 * T ≤ γ) : distI T γ = γ - 2 * T := by
  unfold distI
  have h1 : max (T - γ) (γ - 2 * T) = γ - 2 * T := max_eq_right (by linarith)
  rw [h1, max_eq_right (by linarith)]







lemma LocalCount.A₀_pos {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ : ℝ}
    (h : LocalCount γ m A₀) : 0 < A₀ := lt_of_lt_of_le one_pos h.one_le

end Tail
end Zeta23
end
end

-- from Zeta23.Tail.Count
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/Count.lean — the zero-count sum in the proof of [prop:tail] (the paper §4.2).


Paper, verbatim: "It remains to bound ∑_{γ∉I'} m_ρ D⁻³ (zeros counted with multiplicity).
Zeros with γ > 2T+D₀: grouping them into γ ∈ (2T+D₀+j, 2T+D₀+j+1], j ≥ 0, this part is at
most ∑_{j≥0} A₀ log(2T+D₀+j+4)(D₀+j)⁻³ ≤ (3/2)A₀ log(4T) D₀⁻² for T large (split at j = T
and use D₀ ≥ 2). Zeros with 0 < γ < T−D₀ contribute likewise at most (3/2)A₀ log(4T)D₀⁻²,
and zeros with γ ≤ 0 have D ≥ T and contribute at most ∑_{j≥0} A₀ log(j+4)(T+j)⁻³
≪ T⁻² log T. Altogether ∑_{γ∉I'} m_ρ D⁻³ ≤ 4A₀ log(4T) D₀⁻² for T ≥ T₀."

We prove the bound for every FINITE sub-family of tail zeros (which yields both the
summability and the bound for the full series downstream), with the explicit absolute
threshold T₀ of Zeta23/Tail/Basic.lean. Only the final constant 4 is load-bearing (it is
the 4 in θ₀); we do not follow the paper's intermediate 3/2 + 3/2 + o(1) split. Our
grouping: unit windows indexed by the integer distance j from the nearer endpoint of
I = [T,2T] (lower side: T−j−1 < γ ≤ T−j, which also covers ALL γ ≤ 0; upper side:
2T+j < γ ≤ 2T+j+1), each window weighted by max(D₀, j)⁻³ and counted by the two-sided
local count ≤ A₀ log(2T+4+j); integrals are replaced by telescoping sums.
-/

noncomputable section

open Finset Real

namespace Zeta23
namespace Tail

/-! #### Telescoping sums replacing ∫ x⁻³ and ∫ x⁻² -/








/-! #### Summing the window weights -/


/-! #### One side of the tail, abstractly -/


/-! #### Numerics at T ≥ T₀ -/



/-! #### The zero-count sum -/


/-! #### The boundary count N(I' ∖ I) -/



end Tail
end Zeta23
end
open Finset Real
open Zeta23
open Tail

theorem solution {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ T : ℝ}
    (hN : LocalCount γ m A₀) (hT : T₀ ≤ T) (s : Finset ι) (hs : ∀ ρ ∈ s, InTail T (γ ρ)) :
    ∑ ρ ∈ s, (m ρ : ℝ) * ((distI T (γ ρ)) ^ 3)⁻¹ ≤ 4 * A₀ * Real.log (4 * T) / T := by
  classical
  have hT' : (300 : ℝ) ≤ T := hT
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hA₀ : 0 ≤ A₀ := hN.A₀_pos.le
  set D₀ := Real.sqrt T with hD₀def
  have hD₀ : 17 ≤ D₀ := by
    rw [hD₀def, Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hD₀2 : (2 : ℝ) ≤ D₀ := by linarith
  have hD₀T : D₀ ≤ T := by
    have : D₀ ^ 2 = T := Real.sq_sqrt hT0
    nlinarith
  set B : ℝ := 2 * T + 4 with hBdef
  have hB : (1 : ℝ) ≤ B := by linarith
  -- the common per-side bound
  set W : ℝ := (2 * (D₀ ^ 3)⁻¹ + (D₀ ^ 2)⁻¹ / 2) * Real.log B + (2 * (D₀ ^ 2)⁻¹ + D₀⁻¹) / B
  -- split s into the lower side (γ ≤ T − D₀, includes all γ ≤ 0) and the upper side.
  set slo := s.filter (fun ρ => γ ρ ≤ T - D₀) with hslo
  set shi := s.filter (fun ρ => ¬ γ ρ ≤ T - D₀) with hshi
  have hshi_mem : ∀ ρ ∈ shi, 2 * T + D₀ < γ ρ := by
    intro ρ hρ
    rw [hshi, mem_filter] at hρ
    rcases hs ρ hρ.1 with h | h
    · exact absurd h hρ.2
    · exact h
  have hsplit : ∑ ρ ∈ s, (m ρ : ℝ) * ((distI T (γ ρ)) ^ 3)⁻¹
      = ∑ ρ ∈ slo, (m ρ : ℝ) * ((distI T (γ ρ)) ^ 3)⁻¹
        + ∑ ρ ∈ shi, (m ρ : ℝ) * ((distI T (γ ρ)) ^ 3)⁻¹ :=
    (sum_filter_add_sum_filter_not s _ _).symm
  -- log monotonicity helper: A₀ log(|t|+3) ≤ A₀ log(B + j) when |t| + 3 ≤ B + j
  have hlogmono : ∀ (t : ℝ) (j : ℕ), |t| + 3 ≤ B + j →
      A₀ * Real.log (|t| + 3) ≤ A₀ * Real.log (B + j) := fun t j h =>
    mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) h) hA₀
  ---------------- lower side: x = T − γ, key = ⌊T − γ⌋₊ ----------------
  have hlo : ∑ ρ ∈ slo, (m ρ : ℝ) * ((distI T (γ ρ)) ^ 3)⁻¹ ≤ A₀ * W := by
    have hmem : ∀ ρ ∈ slo, γ ρ ≤ T - D₀ := fun ρ hρ => (mem_filter.mp hρ).2
    have e : ∀ ρ ∈ slo, (m ρ : ℝ) * ((distI T (γ ρ)) ^ 3)⁻¹
        = (m ρ : ℝ) * ((T - γ ρ) ^ 3)⁻¹ := fun ρ hρ => by
      rw [distI_of_le hT0 (by linarith [hmem ρ hρ])]
    rw [sum_congr rfl e]
    apply one_side_sum_le slo (fun ρ => T - γ ρ) m (fun ρ => ⌊T - γ ρ⌋₊) hA₀ hB hD₀2
    · intro ρ hρ; linarith [hmem ρ hρ]
    · intro ρ hρ; exact Nat.floor_le (by linarith [hmem ρ hρ])
    · intro ρ hρ; exact (Nat.lt_floor_add_one _).le
    · intro j
      refine (hN.window (T - j - 1) _ ?_).trans (hlogmono _ _ ?_)
      · intro ρ hρ
        rw [mem_filter] at hρ
        obtain ⟨hρs, hρj⟩ := hρ
        have hnn : 0 ≤ T - γ ρ := by linarith [hmem ρ hρs]
        have := (Nat.floor_eq_iff hnn).mp hρj
        constructor <;> linarith [this.1, this.2]
      · have : |T - j - 1| ≤ T + j + 1 := by
          rw [abs_le]; constructor <;> nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
        rw [hBdef]; linarith
  ---------------- upper side: x = γ − 2T, key = ⌈γ − 2T⌉₊ − 1 ----------------
  have hhi : ∑ ρ ∈ shi, (m ρ : ℝ) * ((distI T (γ ρ)) ^ 3)⁻¹ ≤ A₀ * W := by
    have hmem := hshi_mem
    have e : ∀ ρ ∈ shi, (m ρ : ℝ) * ((distI T (γ ρ)) ^ 3)⁻¹
        = (m ρ : ℝ) * ((γ ρ - 2 * T) ^ 3)⁻¹ := fun ρ hρ => by
      rw [distI_of_ge hT0 (by linarith [hmem ρ hρ])]
    rw [sum_congr rfl e]
    have hceil1 : ∀ ρ ∈ shi, 1 ≤ ⌈γ ρ - 2 * T⌉₊ := fun ρ hρ =>
      Nat.one_le_ceil_iff.mpr (by linarith [hmem ρ hρ])
    have hcast : ∀ ρ ∈ shi, (((⌈γ ρ - 2 * T⌉₊ - 1 : ℕ) : ℝ)) = ⌈γ ρ - 2 * T⌉₊ - 1 :=
      fun ρ hρ => by rw [Nat.cast_sub (hceil1 ρ hρ)]; simp
    apply one_side_sum_le shi (fun ρ => γ ρ - 2 * T) m (fun ρ => ⌈γ ρ - 2 * T⌉₊ - 1)
      hA₀ hB hD₀2
    · intro ρ hρ; linarith [hmem ρ hρ]
    · intro ρ hρ
      rw [hcast ρ hρ]
      have := Nat.ceil_lt_add_one (show 0 ≤ γ ρ - 2 * T by linarith [hmem ρ hρ])
      linarith
    · intro ρ hρ
      rw [hcast ρ hρ]
      have := Nat.le_ceil (γ ρ - 2 * T)
      linarith
    · intro j
      refine (hN.window (2 * T + j) _ ?_).trans (hlogmono _ _ ?_)
      · intro ρ hρ
        rw [mem_filter] at hρ
        obtain ⟨hρs, hρj⟩ := hρ
        have hc : ⌈γ ρ - 2 * T⌉₊ = j + 1 := by have := hceil1 ρ hρs; omega
        have := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).mp hc
        push_cast at this
        constructor <;> linarith [this.1, this.2]
      · rw [abs_of_nonneg (by positivity), hBdef]; linarith
  ---------------- combine ----------------
  rw [hsplit]
  have hnum := two_sides_numeric hT
  calc _ ≤ A₀ * W + A₀ * W := add_le_add hlo hhi
    _ = A₀ * (2 * W) := by ring
    _ ≤ A₀ * (4 * Real.log (4 * T) / T) := mul_le_mul_of_nonneg_left hnum hA₀
    _ = _ := by ring
