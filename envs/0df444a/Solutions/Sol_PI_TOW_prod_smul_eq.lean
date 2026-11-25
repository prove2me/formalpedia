-- Prove2me | solution 1 for PI.TOW.prod_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:29:38.466401+00:00
-- url     : https://prove2.me/submissions/2dc0a76b-6180-4f15-b76b-443257581062

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FilterConcatWLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW
open PI.TO
namespace PI.TOW
theorem _root_.solution {σ K : Type*} [CommRing K] {ι : Type*} [Fintype ι] (c : ι → K) (x : ι → MvPolynomial σ K) :
    ∏ i, (c i • x i) = (∏ i, c i) • ∏ i, x i := by
  simp only [MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]
end PI.TOW
