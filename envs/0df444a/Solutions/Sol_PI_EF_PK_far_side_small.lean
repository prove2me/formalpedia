-- Prove2me | solution 1 for PI.EF.PK.far_side_small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:12.588664+00:00
-- url     : https://prove2.me/submissions/ac787e3f-5df6-4cd8-969f-e3fddef61e37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real
namespace PI.EF.PK
theorem _root_.solution (l x U T ε : ℝ) (hlx : l * x ≤ 0) (hxU : |x| = U) (hT : 0 < T) (hε : 0 < ε)
    (hU0 : 0 < U) (hUe : 2 * T / ε ≤ U) : Real.exp (l * x) / |x| * (2 * T) ≤ ε := by
  rw [hxU]
  have h1 : Real.exp (l * x) ≤ 1 := Real.exp_le_one_iff.2 hlx
  have h2 : Real.exp (l * x) / U * (2 * T) ≤ 1 / U * (2 * T) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact div_le_div_of_nonneg_right h1 hU0.le
  have h3 : 1 / U * (2 * T) ≤ ε := by
    rw [div_le_iff₀ hε] at hUe
    rw [show 1 / U * (2 * T) = 2 * T / U by ring, div_le_iff₀ hU0]
    linarith
  linarith
end PI.EF.PK
