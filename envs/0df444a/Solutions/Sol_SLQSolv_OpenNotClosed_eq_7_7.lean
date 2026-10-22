-- Prove2me | solution 1 for SLQSolv.OpenNotClosed.eq_7_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:58:26.936782+00:00
-- url     : https://prove2.me/submissions/211ec3c6-9433-4d6d-8d8f-7ea74b15dcfb

import Mathlib
import Definitions.Def_SLQSolv_OpenNotClosed_Examples

set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal Matrix

theorem solution (t : ℝ≥0) (ht : t ≤ 1) :
    Tendsto (fun ε : ℝ => ε / (ε + 2 - 2 * (t : ℝ))) (𝓝[>] 0)
      (𝓝 (if t < 1 then 0 else 1)) := by
  have ht' : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  by_cases h : t < 1
  · have h' : (t : ℝ) < 1 := by exact_mod_cast h
    rw [if_pos h]
    have hc : ContinuousAt (fun ε : ℝ => ε / (ε + 2 - 2 * (t : ℝ))) 0 := by
      apply ContinuousAt.div continuousAt_id
      · fun_prop
      · simp; linarith
    have := hc.tendsto
    simp only [zero_div] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have h1 : (t : ℝ) = 1 := by
      have : (1 : ℝ≥0) ≤ t := not_lt.mp h
      have : (1 : ℝ) ≤ t := by exact_mod_cast this
      linarith
    rw [if_neg h]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have : (0 : ℝ) < ε := hε
    rw [h1]
    have e : ε + 2 - 2 * 1 = ε := by ring
    rw [e, div_self this.ne']
