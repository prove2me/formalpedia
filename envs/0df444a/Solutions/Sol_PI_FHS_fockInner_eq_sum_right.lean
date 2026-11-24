-- Prove2me | solution 1 for PI.FHS.fockInner_eq_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:39.331658+00:00
-- url     : https://prove2.me/submissions/dea821a5-57b9-46e2-87b2-3f8e4818bdf9

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Theorems.Thm_PI_FHS_fockInner_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FHS
variable {σ : Type*}
namespace PI.FHS
theorem _root_.solution (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : Q.support ⊆ S) :
    FockH1Action.fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α :=
  fockInner_eq_sum P Q S (fun _ _ hQ => hS (MvPolynomial.mem_support_iff.mpr hQ))
end PI.FHS
