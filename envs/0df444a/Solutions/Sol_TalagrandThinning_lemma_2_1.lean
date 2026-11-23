-- Prove2me | solution 1 for TalagrandThinning.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T06:38:57.2175+00:00
-- url     : https://prove2.me/submissions/79461eb7-bdec-4623-9477-de80afb912ab

import Mathlib
import Definitions.Def_TalagrandThinning_liftL

set_option autoImplicit false

namespace TTL21
open TalagrandThinning

theorem beta_eq (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    beta t p = Real.sqrt (t * (1 - t)) * Real.sqrt (p * (1 - p)) / (p * (1 - t)) := by
  have h1 : (0:ℝ) < 1 - t := by linarith
  have h2 : (0:ℝ) < 1 - p := by linarith
  have hq : 0 < p * (1 - t) := mul_pos hp0 h1
  unfold beta
  rw [eq_div_iff hq.ne', ← Real.sqrt_mul (by positivity)]
  have e : Real.sqrt (t * (1 - p) / (p * (1 - t))) * (p * (1 - t)) =
      Real.sqrt (t * (1 - p) / (p * (1 - t)) * (p * (1 - t)) ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hq.le]
  rw [e]
  congr 1
  field_simp

theorem kernelH_eq (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (x w : Bool) : kernelH t p x w =
      1 + ((if x then 1 else 0) - t) * ((if w then 1 else 0) - p) / (p * (1 - t)) := by
  have h1 : (0:ℝ) < 1 - t := by linarith
  have h2 : (0:ℝ) < 1 - p := by linarith
  have st : 0 < Real.sqrt (t * (1 - t)) := Real.sqrt_pos.mpr (by positivity)
  have sp : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.mpr (by positivity)
  unfold kernelH phi
  rw [beta_eq t p ht0 ht1 hp0 hp1]
  field_simp

end TTL21

open TalagrandThinning in
theorem solution (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ x w : Bool, kernelH t p x w =
      1 + ((if x then 1 else 0) - t) * ((if w then 1 else 0) - p) / (p * (1 - t))) ∧
    kernelH t p false false = 1 / (1 - t) ∧
    kernelH t p false true = (p - t) / (p * (1 - t)) ∧
    kernelH t p true false = 0 ∧
    kernelH t p true true = 1 / p ∧
    (∀ x : Bool, (1 - p) * kernelH t p x false + p * kernelH t p x true = 1) := by
  have h1 : (1:ℝ) - t ≠ 0 := by linarith
  have hp : p ≠ 0 := hp0.ne'
  have E := TTL21.kernelH_eq t p ht0 ht1 hp0 hp1
  refine ⟨E, ?_, ?_, ?_, ?_, ?_⟩
  · rw [E]; simp; field_simp; ring
  · rw [E]; simp; field_simp; ring
  · rw [E]; simp; field_simp; ring
  · rw [E]; simp; field_simp; ring
  · intro x; rw [E, E]; cases x <;> simp <;> field_simp <;> ring
