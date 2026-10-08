-- Prove2me | solution 1 for SuttonBartoRL.Traces.dutch_mc_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:02:27.497712+00:00
-- url     : https://prove2.me/submissions/d12ac839-9ef8-4f8f-b8db-e0334612023f

import Mathlib
import Definitions.Def_SuttonBartoRL_Traces_DutchMC

open SuttonBartoRL.Traces in
theorem dutch_mc_aux_09fb994b {d : ℕ} (α G : ℝ) (x : ℕ → Fin d → ℝ) (w₀ : Fin d → ℝ) :
    ∀ t : ℕ, lmsWeights α G x w₀ (t + 1) = auxVec α x w₀ t + (α * G) • dutchTrace α x t := by
  intro t
  induction t with
  | zero =>
    rw [lmsWeights, lmsWeights, auxVec, dutchTrace]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [dotProduct_comm w₀ (x 0)]
    ring
  | succ n ih =>
    rw [lmsWeights, ih, auxVec, dutchTrace]
    have hdot : (auxVec α x w₀ n + (α * G) • dutchTrace α x n) ⬝ᵥ x (n + 1)
        = x (n + 1) ⬝ᵥ auxVec α x w₀ n + (α * G) * (dutchTrace α x n ⬝ᵥ x (n + 1)) := by
      rw [add_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm (auxVec α x w₀ n)]
    rw [hdot]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

open SuttonBartoRL.Traces in
theorem solution {d : ℕ} (α G : ℝ) (x : ℕ → Fin d → ℝ) (w₀ : Fin d → ℝ)
    (T : ℕ) (hT : 1 ≤ T) :
    lmsWeights α G x w₀ T = auxVec α x w₀ (T - 1) + (α * G) • dutchTrace α x (T - 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
  simpa using dutch_mc_aux_09fb994b α G x w₀ t
