-- Prove2me | solution 1 for PI.BeDiagZp.ContPf.cc_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:13.840414+00:00
-- url     : https://prove2.me/submissions/e0a383e9-3d4e-4658-93ac-9fe8b85789e7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_ConstantCoeffSubstEqZero
import Theorems.Thm_PI_BeDiagZp_ContPf_cc_const
import Theorems.Thm_PI_BeDiagZp_ContPf_cc_mul

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
theorem _root_.solution {σ : Type} {F : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hF : CC F) (k : ℕ) :
    CC fun c => F c ^ k := by
  induction k with
  | zero => simp only [pow_zero]; exact cc_const 1
  | succ k ih => simp only [pow_succ]; exact cc_mul ih hF
end PI.BeDiagZp.ContPf
