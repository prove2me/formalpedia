-- Prove2me | solution 1 for PI.WGL.Fock6.rowDiv_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:40.193014+00:00
-- url     : https://prove2.me/submissions/04fa26a4-6fe3-4cd1-bb83-8a8f6ab078cf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftFock
import Theorems.Thm_PI_WGL_Fock6_weight_rw1_eq_weight_wa
import Theorems.Thm_PI_WGL_Fock6_rowGen_diag_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.REAL MvPolynomial
open PI.WGL.Fock6
namespace PI.WGL.Fock6
theorem _root_.solution {r n : ℕ} (a : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) ℂ) (H : ℤ)
    (hf : IsWeightedHomogeneous (rw1 a) f H) :
    rowDiv ℂ a a k f = ((H.toNat.choose k : ℕ) : ℂ) • f := by
  classical
  unfold rowDiv
  conv_lhs => rw [f.as_sum]
  rw [map_sum, Polynomial.finset_sum_coeff]
  conv_rhs => rw [f.as_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [rowGen_diag_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow]
  have hw := hf (mem_support_iff.mp hm)
  rw [weight_rw1_eq_weight_wa] at hw
  have hw' : Finsupp.weight (wa a) m = H.toNat := by omega
  rw [hw', MvPolynomial.smul_eq_C_mul, map_natCast, mul_comm]
end PI.WGL.Fock6
