-- Prove2me | solution 1 for PeriodicDividend.FixedPoint.L_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:00:03.80014+00:00
-- url     : https://prove2.me/submissions/86c6b7d0-ac50-4c8a-9334-f30052a1d9b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PeriodicDividend_FixedPoint_Model
import Theorems.Thm_PeriodicDividend_FixedPoint_theorem_3_6
import Theorems.Thm_PeriodicDividend_FixedPoint_L_eq_vOneExtended_T

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

open PeriodicDividend.FixedPoint in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ mΩ) (C : ℝ → Ω → ℝ) (p : PeriodicDividend.FixedPoint.Params)
    (hS : p.Standing)
    (hU : PeriodicDividend.FixedPoint.UsualConditions P 𝔽)
    (hC : AtaBarjesteh23.Workload.IsDriftBM 𝔽 P C p.mu p.sigma)
    (A : ℝ) (hA : PeriodicDividend.FixedPoint.Astar p ≤ A) (φ : ℝ≥0 → ℝ)
    (hφ : PeriodicDividend.FixedPoint.CA p A φ)
    (x : ℝ≥0) :
    (0 : EReal) ≤ PeriodicDividend.FixedPoint.Lop P 𝔽 C p φ x ∧
      PeriodicDividend.FixedPoint.Lop P 𝔽 C p φ x ≤
        ((Real.exp (-p.rho * p.T) * (x : ℝ) + A : ℝ) : EReal) := by
  obtain ⟨hρ, hμ, hσ, hF, hP, hT⟩ := hS
  have hS' : p.Standing := ⟨hρ, hμ, hσ, hF, hP, hT⟩
  have hTmem : p.T ∈ Icc (0 : ℝ) p.T := ⟨hT.le, le_rfl⟩
  set e := Real.exp (-p.rho * p.T) with he
  have he0 : 0 < e := Real.exp_pos _
  have hE : 1 < Real.exp (p.rho * p.T) := Real.one_lt_exp_iff.mpr (mul_pos hρ hT)
  have hAs : p.mu * p.T ≤ (Real.exp (p.rho * p.T) - 1) * A := by
    have := hA
    unfold Astar at this
    rw [div_le_iff₀ (by linarith)] at this
    linarith
  have hprod : e * Real.exp (p.rho * p.T) = 1 := by
    rw [he, ← Real.exp_add]; simp
  have hEA : e * (A + p.mu * p.T) ≤ A := by
    calc e * (A + p.mu * p.T) ≤ e * (A + (Real.exp (p.rho * p.T) - 1) * A) :=
          mul_le_mul_of_nonneg_left (by linarith) he0.le
      _ = (e * Real.exp (p.rho * p.T)) * A := by ring
      _ = A := by rw [hprod, one_mul]
  have hlink := L_eq_vOneExtended_T P 𝔽 C p hS' hU hC A φ hφ x
  have h36 := theorem_3_6 P 𝔽 C p hS' hU hC A hA φ hφ
  obtain ⟨hfin, -, -, hCTA, -, -, -, -⟩ := h36
  obtain ⟨hl, hu⟩ := hCTA.2 p.T hTmem x
  have hfx := hfin p.T hTmem x
  rw [hlink, ← EReal.coe_toReal hfx.1 hfx.2]
  have hv : (vOneExtended P 𝔽 C p φ p.T x).toReal = vOne P 𝔽 C p φ p.T x := rfl
  rw [hv]
  have hx := x.2
  refine ⟨?_, ?_⟩
  · rw [← EReal.coe_zero, EReal.coe_le_coe_iff]; nlinarith
  · rw [EReal.coe_le_coe_iff]; nlinarith
