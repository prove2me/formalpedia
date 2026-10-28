-- Prove2me | solution 1 for SolarTariff.Fair.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:26:30.243913+00:00
-- url     : https://prove2.me/submissions/ce307332-7a9e-4455-b1ce-a7fca18a94b7

import Mathlib
import Definitions.Def_SolarTariff_Fair_Model

open SolarTariff.Fair in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Market ι) (τ : T3 ι) (i : ι) (ps : ℝ)
    (hg : 0 < M.g i) (hi : ps ≤ threshold M (τ.bills M) i) :
    0 ≤ M.g i * τ.pr - M.g i * ps - τ.f i := by
  unfold threshold T3.bills gridUsage at hi
  simp only at hi
  rw [le_div_iff₀ hg] at hi
  nlinarith
