-- Prove2me | solution 2 for QuantumMaxCutEnergy.sdp_gap_iff_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T16:57:11.041125+00:00
-- url     : https://prove2.me/submissions/eb7ac3f1-f3d4-41c7-8ff1-61b8da54060b

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Mathlib
open scoped BigOperators

theorem solution
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
