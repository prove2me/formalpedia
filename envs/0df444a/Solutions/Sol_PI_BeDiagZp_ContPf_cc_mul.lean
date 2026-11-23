-- Prove2me | solution 1 for PI.BeDiagZp.ContPf.cc_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:31.580123+00:00
-- url     : https://prove2.me/submissions/823d918a-62a3-4a81-8824-c7de41c3f882

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
    CC fun c => F c * G c := by
  intro n
  simp only [MvPowerSeries.coeff_mul]
  exact continuous_finsetSum _ fun x _ => (hF x.1).mul (hG x.2)
end PI.BeDiagZp.ContPf
