-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreD.aeval_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:27:52.338465+00:00
-- url     : https://prove2.me/submissions/3efcb64f-c840-4233-be20-36aaf3e27d69

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymKEqZeroOfOm
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BoxLeFirstFamily

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreD
variable {m n : ℕ} {ε : Fin m → Bool}
namespace PositivityTheory.Rg.Sw.LC.CoreD
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) (v : V) (h : T v = 0)
    (q : Polynomial ℂ) : Polynomial.aeval T q v = q.eval 0 • v := by
  conv_lhs => rw [← Polynomial.divX_mul_X_add q]
  rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.add_apply, Module.End.mul_apply, h,
    map_zero, zero_add, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
    Polynomial.coeff_zero_eq_eval_zero]
end PositivityTheory.Rg.Sw.LC.CoreD
