-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.expand_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:31.789443+00:00
-- url     : https://prove2.me/submissions/4044cef1-d836-4335-8fe2-7cb1b8b67a46

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_coeff_smul_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreC
theorem _root_.solution {τ : Type} [Fintype τ] [DecidableEq τ] (c : ℂ) (w0 : τ) :
    (c • X w0 : MvPolynomial τ ℂ) = ∑ u, (c • X w0 : MvPolynomial τ ℂ).coeff (Finsupp.single u 1) • X u := by
  simp_rw [coeff_smul_X, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq]; simp
end PositivityTheory.Rg.Sw.LC.CoreC
