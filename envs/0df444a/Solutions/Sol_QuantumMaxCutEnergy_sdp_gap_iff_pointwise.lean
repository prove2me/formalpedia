-- Prove2me | solution 1 for QuantumMaxCutEnergy.sdp_gap_iff_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T16:56:33.388891+00:00
-- url     : https://prove2.me/submissions/4da34b68-da1f-41da-a072-fbb2d1db6ab1

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Mathlib
open scoped BigOperators

/-!
Pointwise form of the semidefinite relaxation bound.

`S` is the least upper bound of the relaxation objectives
`X ↦ ¼ Σᵢⱼ aᵢⱼ (1 - Xᵢⱼ)` over the feasible set (symmetric positive semidefinite with unit
diagonal).  For `C > 0` the scaled inequality `C * S ≤ M` therefore holds exactly when the scaled
objective of every single feasible `X` is at most `M`, because division by the positive `C` turns
the latter condition into "`M / C` is an upper bound of the relaxation objectives", and `S` is the
*least* such bound.

Consequently a target of the shape `0.954 * S ≤ OPT` is equivalent to the pointwise statement that
for every feasible `X` there is a state whose energy is at least `0.954` times the objective of `X`.
The content here is order theory only.
-/

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S C M : ℝ) (hC : 0 < C)
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue A S) :
    C * S ≤ M ↔ ∀ X : Matrix (Fin n) (Fin n) ℝ, ModernConvex.Relaxations.IsUnitDiagPSD X →
      C * ModernConvex.Relaxations.maxcutRelaxationObjective A X ≤ M := by
  set P : Matrix (Fin n) (Fin n) ℝ → ℝ :=
    ModernConvex.Relaxations.maxcutRelaxationObjective A with hP
  set K : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {X | ModernConvex.Relaxations.IsUnitDiagPSD X} with hK
  have hS' : IsLUB (P '' K) S := hS
  constructor
  · -- the bound at `S` propagates to every feasible point, since `C > 0`
    intro h X hX
    have hmem : P X ∈ P '' K := ⟨X, hX, rfl⟩
    have hub : P X ≤ S := hS'.1 hmem
    nlinarith
  · -- `M / C` is an upper bound of the relaxation objectives, so it dominates the least one
    intro h
    have hub : M / C ∈ upperBounds (P '' K) := by
      intro Y hY
      obtain ⟨X, hX, rfl⟩ := hY
      have hx := h X hX
      have hqx : P X ≤ M / C := by
        rw [le_div_iff₀ hC]
        linarith
      simpa only [div_eq_mul_inv] using hqx
    have hle : S ≤ M / C := hS'.2 hub
    rw [le_div_iff₀ hC] at hle
    linarith

#print axioms solution
