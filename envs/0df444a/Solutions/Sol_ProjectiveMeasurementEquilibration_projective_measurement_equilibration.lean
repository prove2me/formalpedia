-- Prove2me | solution 1 for ProjectiveMeasurementEquilibration.projective_measurement_equilibration
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T20:38:52.587834+00:00
-- url     : https://prove2.me/submissions/6f34b2b5-0939-4b19-8089-8474921c9aae

import Definitions.Def_pme_measurement_conditions
import Theorems.Thm_ProjectiveMeasurementEquilibration_eqLind_iff_eqMeas
import Theorems.Thm_ProjectiveMeasurementEquilibration_eqHS_iff_eqMeas
import Theorems.Thm_ProjectiveMeasurementEquilibration_eqKL_iff_eqMeas

open Matrix ProjectiveMeasurementEquilibration

theorem solution {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) (Φ : Matrix n n ℂ → Matrix n n ℂ) :
    (EqMeas hX Φ ↔ EqLind X Φ) ∧ (EqMeas hX Φ ↔ EqHS X Φ) ∧
    (EqMeas hX Φ ↔ EqKL X Φ) :=
  ⟨(eqLind_iff_eqMeas hX Φ).symm, (eqHS_iff_eqMeas hX Φ).symm,
    (eqKL_iff_eqMeas hX Φ).symm⟩
