-- Prove2me | solution 1 for QuantumLTF.Membership.centerPhaseGate_unitary
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-14T21:22:37.070676+00:00
-- url     : https://prove2.me/submissions/354d44c9-f2f0-4e90-a6f2-6ae808beb8ea

import Mathlib
import Definitions.Def_QuantumLTF_Membership_centerPhaseGate

private lemma exp_phase_mul_star (x : ℂ) (hx : (starRingEnd ℂ) x = x) :
    Complex.exp (2 * Real.pi * Complex.I * x) *
      star (Complex.exp (2 * Real.pi * Complex.I * x)) = 1 := by
  change Complex.exp (2 * Real.pi * Complex.I * x) *
    (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * x)) = 1
  rw [← Complex.exp_conj]
  have h : (starRingEnd ℂ) (2 * Real.pi * Complex.I * x) =
      -(2 * Real.pi * Complex.I * x) := by
    rw [map_mul, map_mul, map_mul]
    rw [map_ofNat, hx]
    norm_num
  rw [h, ← Complex.exp_add]
  simp

theorem solution (b : ℕ) (i : Fin b) :
    QuantumLTF.Membership.centerPhaseGate b i ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext y z
  cases y <;> cases z <;>
    simp [QuantumLTF.Membership.centerPhaseGate, Matrix.mul_apply] <;>
    apply exp_phase_mul_star <;>
    simp [map_ofNat]
