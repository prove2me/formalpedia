-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.local_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:34:49.692846+00:00
-- url     : https://prove2.me/submissions/f2b6e68a-fbe1-47c7-848d-4c459ed589f0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_SkewApprox
import Definitions.Def_Lemmata_GeneralBFactRightTer_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Assembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork
namespace PI.UnitaryApproxFinWork
theorem _root_.solution {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (h2 : IsUnit (2 : R)) (g X XR W : Matrix n n R)
    (hXP : (1 + X) * (1 + g) = 2) (hΔ : (XR - X) * (1 + g) = (2 : R) • W) (hW : IsUnit (1 + W).det) :
    IsUnit (1 + XR).det := by
  have h2m : (2 : Matrix n n R) = (2 : R) • 1 := by rw [two_smul, one_add_one_eq_two]
  have hQP : (1 + XR) * (1 + g) = (2 : R) • (1 + W) := by
    have : 1 + XR = (1 + X) + (XR - X) := by abel
    rw [this, Matrix.add_mul, hXP, hΔ, h2m, smul_add]
  have hd := congrArg Matrix.det hQP
  rw [Matrix.det_mul, Matrix.det_smul] at hd
  have hu : IsUnit ((1 + XR).det * (1 + g).det) := by
    rw [hd]; exact (h2.pow _).mul hW
  exact isUnit_of_mul_isUnit_left hu
end PI.UnitaryApproxFinWork
