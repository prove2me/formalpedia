-- Prove2me | solution 1 for PI.WMI.det_ne_zero_of_mem_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:10:33.230332+00:00
-- url     : https://prove2.me/submissions/cd8cbfd9-bcd0-4ab7-a58b-b6bc504e18b9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_Assembly

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
theorem _root_.solution {N : ℕ} {g : Matrix (Fin N) (Fin N) ℂ} (hg : g ∈ Kset (allPos N)) :
    g.det ≠ 0 := by
  have h1 := hg.1
  rw [Matrix.mem_unitaryGroup_iff] at h1
  intro h0
  have := congrArg Matrix.det h1
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this
end PI.WMI
