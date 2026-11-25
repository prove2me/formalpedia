-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.iteratedDeriv_poly_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:18.194837+00:00
-- url     : https://prove2.me/submissions/00bc931d-05e3-49f3-9d69-f3a7f89b9369

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivPolyRealZero

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
    iteratedDeriv k (fun t : ℝ => p.eval (t : ℂ)) = fun t : ℝ => (Polynomial.derivative^[k] p).eval (t : ℂ) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    have hd : deriv (fun t : ℝ => p.eval (t : ℂ)) = fun t : ℝ => (Polynomial.derivative p).eval (t : ℂ) := by
      funext t
      exact ((Polynomial.hasDerivAt p (t : ℂ)).comp_ofReal).deriv
    rw [iteratedDeriv_succ', hd, ih]
    funext t
    rw [Function.iterate_succ_apply]
end PositivityTheory.SiegelWeilFormula.KFPB
