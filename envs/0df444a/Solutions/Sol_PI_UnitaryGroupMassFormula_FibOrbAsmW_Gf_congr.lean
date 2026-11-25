-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FibOrbAsmW.Gf_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:20.233705+00:00
-- url     : https://prove2.me/submissions/55e5e66b-3dde-4582-bcd8-0f040a76756f

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FibreOrbits_FibreOrbitOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FibOrbAsmW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
namespace PI.UnitaryGroupMassFormula.FibOrbAsmW
theorem _root_.solution {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g₁ g₂ : B.Mat k r}
    (hZ : Zhat k r z z' g₁ = Zhat k r z z' g₂) : Gf k r z z' g₂ = Gf k r z z' g₁ := by
  unfold Gf Dmin
  rw [hZ]
end PI.UnitaryGroupMassFormula.FibOrbAsmW
