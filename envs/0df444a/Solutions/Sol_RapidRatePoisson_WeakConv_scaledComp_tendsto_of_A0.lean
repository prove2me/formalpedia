-- Prove2me | solution 1 for RapidRatePoisson.WeakConv.scaledComp_tendsto_of_A0
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T11:13:32.178825+00:00
-- url     : https://prove2.me/submissions/9e0c2153-b145-4066-9c70-fc171bbfc7bf

import Mathlib
import Definitions.Def_RapidRatePoisson_WeakConv_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open RapidRatePoisson.WeakConv

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : ℝ≥0 → Ω → ℝ) (lamStar : ℝ≥0)
    (hA0 : ∀ ω, A 0 ω = 0) (hA1 : Assumption1 P A lamStar) (t : ℝ≥0) :
    TendstoInMeasure P (fun (ε : ℝ≥0) ω => scaledComp A ε t ω) (𝓝[>] 0)
      (fun _ => (lamStar : ℝ) * t) := by
  intro δ hδ
  rcases eq_or_lt_of_le (zero_le (a := t)) with ht | ht
  · -- t = 0: everything vanishes
    subst ht
    apply tendsto_const_nhds.congr'
    filter_upwards with ε
    have : {x : Ω | δ ≤ edist (scaledComp A ε 0 x) ((lamStar : ℝ) * ((0 : ℝ≥0) : ℝ))} = ∅ := by
      ext x
      simp only [scaledComp, zero_div, hA0, mul_zero, NNReal.coe_zero, edist_self,
        Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact hδ
    rw [this, measure_empty]
  · have htr : (0 : ℝ) < t := by exact_mod_cast ht
    -- the time `t / ε` tends to infinity
    have hT : Tendsto (fun ε : ℝ≥0 => t / ε) (𝓝[>] 0) atTop := by
      rw [tendsto_atTop]
      intro M
      have hpos : (0 : ℝ≥0) < t / (M + 1) := div_pos ht (by positivity)
      filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
      obtain ⟨hε0, hε1⟩ := hε
      rw [le_div_iff₀ hε0]
      have h1 : ε * (M + 1) ≤ t := by
        have := hε1; rw [lt_div_iff₀ (by positivity)] at this; exact this.le
      calc M * ε ≤ (M + 1) * ε := by gcongr; exact le_self_add
        _ = ε * (M + 1) := mul_comm _ _
        _ ≤ t := h1
    -- rescale the tolerance
    set δ' : ℝ≥0∞ := δ / ENNReal.ofReal t with hδ'
    have htne : ENNReal.ofReal t ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact htr
    have httop : ENNReal.ofReal t ≠ ⊤ := ENNReal.ofReal_ne_top
    have hδ'pos : 0 < δ' := ENNReal.div_pos hδ.ne' httop
    have h := (hA1.2 δ' hδ'pos).comp hT
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (0 : ℝ) < ε := by exact_mod_cast hε
    simp only [Function.comp]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, scaledComp]
    have hkey : edist ((ε : ℝ) * A (t / ε) x) ((lamStar : ℝ) * t) =
        ENNReal.ofReal t * edist (A (t / ε) x / ((t / ε : ℝ≥0) : ℝ)) (lamStar : ℝ) := by
      rw [edist_dist, edist_dist, ← ENNReal.ofReal_mul htr.le]
      congr 1
      rw [Real.dist_eq, Real.dist_eq, NNReal.coe_div]
      have : (ε : ℝ) * A (t / ε) x - lamStar * t = t * (A (t / ε) x / (t / ε) - lamStar) := by
        field_simp
      rw [this, abs_mul, abs_of_pos htr]
    rw [hkey, hδ', ENNReal.div_le_iff htne httop, mul_comm]
