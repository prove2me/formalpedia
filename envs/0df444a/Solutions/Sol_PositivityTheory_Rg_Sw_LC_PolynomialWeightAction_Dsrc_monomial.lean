-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.Dsrc_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:52:49.695333+00:00
-- url     : https://prove2.me/submissions/203855ed-2a4c-4fd4-a090-c747f49f744c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_TransvectionInv
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_Dsrc_diag_X
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_wgt_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_wgt_single

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
theorem _root_.solution (l : Fin n) (d : FinalTheorems m n →₀ ℕ) (r : ℂ) :
    Dsrc (m := m) l l (monomial d r) = C ((wgt l d : ℤ) : ℂ) * monomial d r := by
  induction d using Finsupp.induction with
  | zero =>
    rw [monomial_zero', MvPolynomial.derivation_C]; simp [wgt]
  | single_add v k f _ hk ih =>
    rw [monomial_single_add, Derivation.leibniz, ih, Derivation.leibniz_pow, Dsrc_diag_X, wgt_add,
      wgt_single l k v]
    have hX : (X v : MvPolynomial (FinalTheorems m n) ℂ) ^ (k - 1) * X v = X v ^ k := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk)]
    simp only [smul_eq_mul, nsmul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast, map_add, map_mul,
      map_natCast]
    calc _ = (k : MvPolynomial (FinalTheorems m n) ℂ) * C ((wgt l (Finsupp.single v 1) : ℤ) : ℂ) * (X v ^ (k - 1) * X v) *
            monomial f r + C ((wgt l f : ℤ) : ℂ) * (X v ^ k * monomial f r) := by ring
      _ = _ := by rw [hX]; ring
end PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
