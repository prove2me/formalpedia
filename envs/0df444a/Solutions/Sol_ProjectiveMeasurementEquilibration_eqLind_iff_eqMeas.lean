-- Prove2me | solution 1 for ProjectiveMeasurementEquilibration.eqLind_iff_eqMeas
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T19:33:25.661049+00:00
-- url     : https://prove2.me/submissions/6b9d04ee-fcc6-42a5-b5c1-feb2e02d443e

import Definitions.Def_pme_measurement_conditions
import Theorems.Thm_ProjectiveMeasurementEquilibration_lindblad_tendsto_pinching

open Matrix Filter Topology ProjectiveMeasurementEquilibration

theorem solution {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) (Φ : Matrix n n ℂ → Matrix n n ℂ) :
    EqLind X Φ ↔ EqMeas hX Φ := by
  constructor
  · intro h ρ hρ
    obtain ⟨ρt, hsol⟩ := (h ρ hρ).1
    exact tendsto_nhds_unique ((h ρ hρ).2 ρt hsol)
      ((lindblad_tendsto_pinching hX ρ hρ).2 ρt hsol)
  · intro h ρ hρ
    obtain ⟨hexists, hlimit⟩ := lindblad_tendsto_pinching hX ρ hρ
    refine ⟨hexists, ?_⟩
    intro ρt hsol
    rw [h ρ hρ]
    exact hlimit ρt hsol
