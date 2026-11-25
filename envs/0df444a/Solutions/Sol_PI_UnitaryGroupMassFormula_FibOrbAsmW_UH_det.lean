-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FibOrbAsmW.UH_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:00:42.194564+00:00
-- url     : https://prove2.me/submissions/23c98bfc-a68a-432e-a7ad-bcfecff16929

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace PI.UnitaryGroupMassFormula.FibOrbAsmW
theorem _root_.solution {H g : Matrix ι ι ℂ} (hH : IsUnit H.det) (hg : g ∈ UH H) : IsUnit g.det := by
  have hg' : gᴴ * H * g = H := hg
  have := congrArg Matrix.det hg'
  rw [det_mul, det_mul, det_conjTranspose] at this
  rw [isUnit_iff_ne_zero] at hH ⊢
  intro h0
  rw [h0, mul_zero] at this
  exact hH this.symm
end PI.UnitaryGroupMassFormula.FibOrbAsmW
