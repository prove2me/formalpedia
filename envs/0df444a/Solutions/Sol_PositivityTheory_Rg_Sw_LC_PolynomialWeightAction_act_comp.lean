-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.act_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:45:26.777623+00:00
-- url     : https://prove2.me/submissions/299057e4-71c9-4acb-8384-045115a00ee9

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_TransvectionInv

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
theorem _root_.solution (A B : Matrix (Fin n) (Fin n) ℂ) :
    act (m := m) (B * A) = (act A).comp (act B) := by
  apply MvPolynomial.algHom_ext
  rintro (⟨l, a⟩ | ⟨l, b⟩)
  · simp only [act, AlgHom.comp_apply, aeval_X, Sum.elim_inl, map_sum, map_mul, aeval_C,
      MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  · simp only [act, AlgHom.comp_apply, aeval_X, Sum.elim_inr, map_sum, map_mul, aeval_C,
      MvPolynomial.algebraMap_eq, Matrix.mul_inv_rev, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum,
      mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    ring
end PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
