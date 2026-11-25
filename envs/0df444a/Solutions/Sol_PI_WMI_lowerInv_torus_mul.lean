-- Prove2me | solution 1 for PI.WMI.lowerInv_torus_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:21.373899+00:00
-- url     : https://prove2.me/submissions/a8da177f-20bb-466b-9570-cd1d8f9ea37c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_LowerInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
namespace PI.WMI
theorem _root_.solution {N : ℕ} (θ φ : Fin N → ℝ) : torus θ * torus φ = torus (θ + φ) := by
  unfold torus
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Complex.exp_add]
  congr 1
  push_cast [Pi.add_apply]
  ring
end PI.WMI
