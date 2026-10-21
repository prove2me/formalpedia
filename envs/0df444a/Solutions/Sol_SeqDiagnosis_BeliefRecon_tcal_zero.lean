-- Prove2me | solution 1 for SeqDiagnosis.BeliefRecon.tcal_zero
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T09:57:33.474324+00:00
-- url     : https://prove2.me/submissions/bb322341-c839-4467-827b-7472266db675

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Model

open Matrix SeqDiagnosis.BeliefRecon

theorem solution {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (hS : M.Standing) (hETM : M.ETM)
    (R : Matrix (Fin N) (Fin r) ℝ) (P : Matrix (Fin r) (Fin p) ℝ)
    (θ : Fin (N + 1) → ℝ) (hθ : θ ∈ stdSimplex ℝ (Fin (N + 1)))
    (t : ℕ) (x : Fin r → ℝ) :
    Tcal M R P t x θ 0 = θ 0 /
      (θ 0 + ∑ i : Fin N, θ i.succ * Real.exp ((t : ℝ) * (betaZero M R P i + (R *ᵥ x) i))) ∧
    (∑ k, Tcal M R P t x θ k) = 1 := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  set w : Fin N → ℝ := fun i => θ i.succ * Real.exp ((t : ℝ) * (betaZero M R P i + (R *ᵥ x) i))
    with hw
  have hwnn : ∀ i, 0 ≤ w i := fun i => mul_nonneg (hθ0 _) (Real.exp_pos _).le
  have hD : 0 < θ 0 + ∑ i, w i := by
    rcases (add_nonneg (hθ0 0) (Finset.sum_nonneg (fun i _ => hwnn i))).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : θ 0 = 0 := by
        have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hwnn i)
        linarith [hθ0 0]
      have hs : ∑ i, w i = 0 := by rw [h0] at h; linarith
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hwnn i)] at hs
      have : ∀ i : Fin N, θ i.succ = 0 := by
        intro i
        have := hs i (Finset.mem_univ _)
        simp only [hw] at this
        rcases mul_eq_zero.mp this with h' | h'
        · exact h'
        · exact absurd h' (Real.exp_pos _).ne'
      rw [Fin.sum_univ_succ, h0] at hθ1
      simp [this] at hθ1
  refine ⟨?_, ?_⟩
  · simp only [Tcal, Fin.cases_zero]
    rw [← hw, ← Finset.sum_div]
    field_simp
    ring
  · rw [Fin.sum_univ_succ]
    simp only [Tcal, Fin.cases_zero, Fin.cases_succ]
    ring
