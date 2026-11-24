-- Prove2me | solution 1 for PI.OddDualWeyl.invT_invT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:08.966176+00:00
-- url     : https://prove2.me/submissions/9b17401b-6f81-43e8-8c8d-2391467756d0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_RevColOneTranspose

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
variable {K : Type} [Field K]
namespace PI.OddDualWeyl
theorem _root_.solution {n : ℕ} {g : Matrix (Fin n) (Fin n) K} (hg : IsUnit g.det) : (((g⁻¹)ᵀ)⁻¹)ᵀ = g := by
  have h1 : IsUnit (gᵀ).det := by rwa [det_transpose]
  rw [transpose_nonsing_inv g, nonsing_inv_nonsing_inv _ h1, transpose_transpose]
end PI.OddDualWeyl
