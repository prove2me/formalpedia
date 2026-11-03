-- Prove2me | solution 1 for QuantumMaxCutEnergy.agm_classical_sdp_rank_three_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T16:59:28.78091+00:00
-- url     : https://prove2.me/submissions/8b99e222-9ea1-4341-87e4-14d0043c1e01

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Theorems.Thm_QuantumMaxCutEnergy_rank_three_rounding_pointwise
import Mathlib
open scoped BigOperators

theorem sdp_gap_iff_pointwise
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S C M : ℝ) (hC : 0 < C)
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue A S) :
    C * S ≤ M ↔ ∀ X : Matrix (Fin n) (Fin n) ℝ, ModernConvex.Relaxations.IsUnitDiagPSD X →
      C * ModernConvex.Relaxations.maxcutRelaxationObjective A X ≤ M := by
  constructor
  · intro hSS X hX
    exact (mul_le_mul_of_nonneg_left (hS.1 (Set.mem_image_of_mem _ hX)) hC.le).trans hSS
  · intro h
    have hUB : M / C ∈ upperBounds ((fun X : Matrix (Fin n) (Fin n) ℝ =>
        ModernConvex.Relaxations.maxcutRelaxationObjective A X) ''
          {X | ModernConvex.Relaxations.IsUnitDiagPSD X}) := by
      rintro _ ⟨X, hX, rfl⟩
      rw [le_div_iff₀ hC]
      linarith [h X hX]
    have hSle : S ≤ M / C := by
      have h' := hS.upperBounds_eq
      rw [h'] at hUB
      exact hUB
    calc C * S ≤ C * (M / C) := mul_le_mul_of_nonneg_left hSle hC.le
      _ = M := by field_simp

theorem solution (G : QuantumMaxCutEnergy.Input) (S : ℝ)
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue
      (Matrix.of fun i j : Fin G.n =>
        if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
        else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S) :
    (0.954 : ℝ) * S ≤ QuantumMaxCutEnergy.optimum G :=
  (sdp_gap_iff_pointwise _ S 0.954 (QuantumMaxCutEnergy.optimum G) (by norm_num) hS).mpr
    (fun X hX => QuantumMaxCutEnergy.rank_three_rounding_pointwise G X hX)
