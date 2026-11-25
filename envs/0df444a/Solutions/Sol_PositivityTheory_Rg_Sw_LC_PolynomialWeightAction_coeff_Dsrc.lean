-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.coeff_Dsrc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:54.35638+00:00
-- url     : https://prove2.me/submissions/5705f759-4854-41b1-a1bb-bce5e0ec708f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_TransvectionInv
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_Dsrc_monomial

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
theorem _root_.solution (l : Fin n) (p : MvPolynomial (FinalTheorems m n) ℂ) (d : FinalTheorems m n →₀ ℕ) :
    coeff d (Dsrc (m := m) l l p) = ((wgt l d : ℤ) : ℂ) * coeff d p := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum, coeff_sum]
  simp only [Dsrc_monomial, coeff_C_mul, coeff_monomial]
  rw [Finset.sum_eq_single d]
  · simp
  · intro b _ hb; simp [hb]
  · intro hd; simp [MvPolynomial.notMem_support_iff.mp hd]
end PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
