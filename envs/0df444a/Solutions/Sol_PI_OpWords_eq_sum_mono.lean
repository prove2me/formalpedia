-- Prove2me | solution 1 for PI.OpWords.eq_sum_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:01:49.436281+00:00
-- url     : https://prove2.me/submissions/5fa132b9-2494-4326-9b2e-2308c1dc1136

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaCoeff
import Theorems.Thm_PI_OpWords_mono_val
import Theorems.Thm_PI_OpWords_degree_of_coeff_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
open PI PI.OpWords
variable {K : Type} [Field K] {k d : ℕ}
namespace PI.OpWords
theorem _root_.solution (F : ↥(homogeneousSubmodule (Fin k) K d)) :
    F = ∑ g ∈ (F : MvPolynomial (Fin k) K).support,
      coeff g (F : MvPolynomial (Fin k) K) • mono K k d g := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  conv_lhs => rw [(F : MvPolynomial (Fin k) K).as_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [Submodule.coe_smul, mono_val, if_pos (degree_of_coeff_ne F (MvPolynomial.mem_support_iff.1 hg)),
    smul_monomial, smul_eq_mul, mul_one]
end PI.OpWords
