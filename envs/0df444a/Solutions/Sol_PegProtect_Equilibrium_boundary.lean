-- Prove2me | solution 1 for PegProtect.Equilibrium.boundary
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T19:57:21.938393+00:00
-- url     : https://prove2.me/submissions/8f31558d-5f2f-4dd8-a5de-19e465d8a230

import Mathlib
import Definitions.Def_PegProtect_Equilibrium_Model
open PegProtect.Equilibrium

theorem solution(P : Params) (hP : P.Standing) :
    omegaHat P < 1 ∧ (omegaHat P ≤ 0 → piP P 0 ≤ piM P 0) := by
  obtain ⟨hc, hd0, hd1, hphi, hδ, hρ, hν⟩ := hP
  have hb0 : 0 < P.beta := Real.exp_pos _
  have hb1 : P.beta < 1 := by
    unfold Params.beta; rw [Real.exp_lt_one_iff]; have := div_pos hδ hρ; linarith
  have hbi : 1 < P.beta⁻¹ := one_lt_inv_iff₀.2 ⟨hb0, hb1⟩
  have h1d : 0 < 1 - P.d := by linarith
  refine ⟨?_, ?_⟩
  · unfold omegaHat
    rw [div_lt_one h1d]
    nlinarith
  · intro h
    unfold omegaHat at h
    rw [div_nonpos_iff] at h
    have hle : P.phi - P.d ≤ P.beta⁻¹ * (P.phi - 1) := by
      rcases h with ⟨_, h2⟩ | ⟨h1, h2⟩
      · linarith
      · linarith
    have hA : ∑' n : ℕ, q 0 (-((n : ℤ) + 1)) = 0 := by
      have : ∀ n : ℕ, q 0 (-((n : ℤ) + 1)) = 0 := by
        intro n
        simp only [q]
        have : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
        rw [this]; simp
      rw [show (fun n : ℕ => q 0 (-((n : ℤ) + 1))) = fun _ => 0 from funext this]; simp
    have hB : ∑' n : ℕ, q 0 n * P.beta ^ (n + 1) = P.beta := by
      rw [tsum_eq_single 0]
      · simp [q]
      · intro n hn; simp [q, hn]
    have hC : ∑' n : ℕ, q 0 n = 1 := by
      rw [tsum_eq_single 0]
      · simp [q]
      · intro n hn; simp [q, hn]
    unfold piP piM
    rw [hA, hB, hC]
    have := mul_le_mul_of_nonneg_left hle hb0.le
    rw [← mul_assoc, mul_inv_cancel₀ hb0.ne'] at this
    nlinarith
