-- Prove2me | solution 1 for PI.BeDiagZp.ContPf.zc_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:14.285797+00:00
-- url     : https://prove2.me/submissions/00e1bf85-5c7c-4923-9393-167664059a8a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_ConstantCoeffSubstEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BeDiagZp PI.BeDiagZp.ContPf
variable {p : ℕ} [Fact p.Prime]
namespace PI.BeDiagZp.ContPf
theorem _root_.solution : Continuous (zc : ℤ_[p] → ℂ_[p]) := by
  unfold zc
  exact (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val
end PI.BeDiagZp.ContPf
