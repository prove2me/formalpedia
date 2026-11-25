-- Prove2me | solution 1 for PI.FJMB.diagonal_hypothesis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:46:26.593807+00:00
-- url     : https://prove2.me/submissions/41c604d4-930d-44a9-b37e-2973ecc8aae0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurCauchy
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_DiagonalImageBlockFree
import Theorems.Thm_PI_FJMB_cd_mono_factor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}
namespace PI.FJMB
theorem _root_.solution : HypDiag := by
  intro σ m ι hι α P hP
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hm : MvPolynomial.monomial e (P.coeff e) = MvPolynomial.C (P.coeff e) * MvPolynomial.monomial e 1 := by
    rw [MvPolynomial.C_mul_monomial, mul_one]
  rw [hm, map_mul, map_mul, cd_mono_factor ι hι e]
  have hs : ∀ i, ∑ k : Fin m, e (ι (i, k)) = α i := hP e he
  simp only [hs, MvPolynomial.aeval_C]
  ring
end PI.FJMB
