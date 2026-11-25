-- Prove2me | solution 1 for PI.WHw.bC_rowGen_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:42:17.678208+00:00
-- url     : https://prove2.me/submissions/7020c23e-5813-49ba-b018-1195757968ed

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ClosedEqNablaC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_BCRowGenMonomial
import Theorems.Thm_PI_WHw_bC_rowGen_X
import Theorems.Thm_PI_WHw_bC_rowGen_C
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
open PI PI.WHw
namespace PI.WHw
theorem _root_.solution {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : ℂ) :
    rowGen ℂ a a (monomial m c) =
      Polynomial.C (monomial m c) * (1 + Polynomial.X) ^ (Finsupp.weight (lgraded_wa a) m) := by
  induction m using Finsupp.induction
  next =>
    rw [MvPolynomial.monomial_zero', bC_rowGen_C]
    simp
  next v e m _ _ ih =>
    rw [MvPolynomial.monomial_single_add, map_mul, map_pow, bC_rowGen_X, ih]
    have hw : Finsupp.weight (lgraded_wa a) (Finsupp.single v e + m) =
        e * lgraded_wa a v + Finsupp.weight (lgraded_wa a) m := by
      simp [map_add, Finsupp.weight_apply, Finsupp.sum_single_index]
    rw [hw]
    simp only [map_mul, map_pow]
    ring
end PI.WHw
