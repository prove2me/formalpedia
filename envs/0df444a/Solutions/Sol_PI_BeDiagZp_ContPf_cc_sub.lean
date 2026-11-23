-- Prove2me | solution 1 for PI.BeDiagZp.ContPf.cc_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:11.440297+00:00
-- url     : https://prove2.me/submissions/e7345321-755f-48a6-8625-955bd6c92a44

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
theorem _root_.solution {σ : Type} {F G : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hF : CC F) (hG : CC G) :
    CC fun c => F c - G c := by
  intro n; simp only [map_sub]; exact (hF n).sub (hG n)
end PI.BeDiagZp.ContPf
