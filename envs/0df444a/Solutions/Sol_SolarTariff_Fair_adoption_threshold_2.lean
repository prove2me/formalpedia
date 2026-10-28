-- Prove2me | solution 2 for SolarTariff.Fair.adoption_threshold
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:21:49.510673+00:00
-- url     : https://prove2.me/submissions/03d0b9b3-78a6-4c17-96e0-192d7c71aae7

import Mathlib
import Definitions.Def_SolarTariff_Fair_Model

open SolarTariff.Fair in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Market ι) (B : Bills ι) (i : ι) (ps : ℝ) (hg : 0 < M.g i) :
    (B.adopt i + ps * M.g i ≤ B.nonAdopt i ↔ ps ≤ threshold M B i) ∧
    (i ∈ adopters M B ps ↔ B.adopt i + ps * M.g i ≤ B.nonAdopt i) := by
  have h1 : B.adopt i + ps * M.g i ≤ B.nonAdopt i ↔ ps ≤ threshold M B i := by
    unfold threshold
    rw [le_div_iff₀ hg]
    constructor <;> intro h <;> linarith
  refine ⟨h1, ?_⟩
  unfold adopters
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact h1.symm
