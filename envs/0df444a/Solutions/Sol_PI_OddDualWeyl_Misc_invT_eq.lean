-- Prove2me | solution 1 for PI.OddDualWeyl.Misc.invT_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:58:51.027536+00:00
-- url     : https://prove2.me/submissions/1506aceb-2877-44bf-9480-2c9399fca970

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_ExistsEqMulOfColumnSpanLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open PI.OddDualWeyl.Misc
variable {O K : Type} [CommRing O] [Field K] [Algebra O K]
namespace PI.OddDualWeyl.Misc
theorem _root_.solution {n : ℕ} {g g' : Matrix (Fin n) (Fin n) K} (hg : IsUnit g.det) (hg' : IsUnit g'.det)
    (u : Matrix (Fin n) (Fin n) O) (hu : g' = g * u.map (algebraMap O K)) :
    (g⁻¹)ᵀ = (g'⁻¹)ᵀ * (uᵀ).map (algebraMap O K) := by
  have hU : g⁻¹ * g' = u.map (algebraMap O K) := by
    rw [hu, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hg, Matrix.one_mul]
  have hinv : g⁻¹ = u.map (algebraMap O K) * g'⁻¹ := by
    rw [← hU, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg', Matrix.mul_one]
  rw [hinv, Matrix.transpose_mul, Matrix.transpose_map]
end PI.OddDualWeyl.Misc
