-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.coeff_smul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:10.6922+00:00
-- url     : https://prove2.me/submissions/bc73546e-ac04-4297-babd-4023a8a13840

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX

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
theorem _root_.solution {τ : Type} [DecidableEq τ] (c : ℂ) (w0 u : τ) :
    (c • X w0 : MvPolynomial τ ℂ).coeff (Finsupp.single u 1) = if w0 = u then c else 0 := by
  rw [coeff_smul, coeff_X']
  by_cases h : w0 = u
  · subst h; simp
  · rw [if_neg (fun e => h ((Finsupp.single_left_inj one_ne_zero).mp e)), if_neg h]; simp
end PositivityTheory.Rg.Sw.LC.CoreC
