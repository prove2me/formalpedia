-- Prove2me | solution 1 for Plasticity.Ext.KMRate
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T17:56:24.073438+00:00
-- url     : https://prove2.me/submissions/ff8039c9-4380-4a0d-bd0b-dfb2bd0e0ef9

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.EMetricSpace.Lipschitz
import Theorems.Thm_Plasticity_Ext_KMRate_binomial_bound
import Theorems.Thm_Plasticity_Ext_KMRate_binomial_sum_le

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hconv : Convex ℝ C) (D : ℝ) (hD : ∀ x ∈ C, ∀ y ∈ C, ‖x - y‖ ≤ D)
    (K : E → E) (hmaps : Set.MapsTo K C C) (hlip : LipschitzOnWith 1 K C)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) (hn : 1 ≤ n) (x : E) (hx : x ∈ C) :
    ‖(fun z => (1 - α) • z + α • K z)^[n] x - K ((fun z => (1 - α) • z + α • K z)^[n] x)‖
      ≤ D / Real.sqrt (Real.pi * n * α * (1 - α)) := by
  have h1 := Plasticity.Ext.KMRate.binomial_bound C hconv D hD K hmaps hlip α hα0 hα1 n x hx
  set u : ℝ := 2 * α * (1 - α) with hu
  have hβ : 0 < 1 - α := by linarith
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 / 2 := by nlinarith [sq_nonneg (2 * α - 1)]
  have h2 := Plasticity.Ext.KMRate.binomial_sum_le n u hu0.le hu1
  set S := ∑ m ∈ Finset.range (n + 1),
    (n.choose m : ℝ) * u ^ m * (1 - u) ^ (n - m) * ((m.choose (m / 2) : ℝ) / 2 ^ m) with hS
  have hD0 : 0 ≤ D := by simpa using hD x hx x hx
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnu : 0 < Real.sqrt (n * u) := Real.sqrt_pos.mpr (by positivity)
  have hq : 0 < Real.pi * n * α * (1 - α) := by have := Real.pi_pos; positivity
  have hS' : S ≤ Real.sqrt (2 / Real.pi) / Real.sqrt (n * u) := by
    rw [le_div_iff₀ hnu]; linarith [h2]
  have heq : Real.sqrt (2 / Real.pi) / Real.sqrt (n * u)
      = 1 / Real.sqrt (Real.pi * n * α * (1 - α)) := by
    rw [← Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ n * u),
      one_div, ← Real.sqrt_inv]
    congr 1
    have := Real.pi_pos
    rw [hu]; field_simp
  calc _ ≤ D * S := h1
    _ ≤ D * (1 / Real.sqrt (Real.pi * n * α * (1 - α))) := by
        rw [← heq]; exact mul_le_mul_of_nonneg_left hS' hD0
    _ = _ := by ring
