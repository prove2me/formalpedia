-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.iteratedDeriv_poly_real_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:24.025021+00:00
-- url     : https://prove2.me/submissions/db7171f5-d325-4f7d-a88c-bf234a8ce1e2

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivPolyRealZero
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_iteratedDeriv_poly_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.SiegelWeilFormula.KFPB
theorem _root_.solution (p : Polynomial ℂ) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => p.eval (t : ℂ)) 0 = (k.factorial : ℂ) * p.coeff k := by
  rw [iteratedDeriv_poly_real]
  simp only [Complex.ofReal_zero]
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative, zero_add,
    Nat.descFactorial_self, nsmul_eq_mul]
end PositivityTheory.SiegelWeilFormula.KFPB
