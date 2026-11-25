-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.contr_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:42:02.042309+00:00
-- url     : https://prove2.me/submissions/06e799c8-b26a-47c7-a70e-7c1cd9284bde

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_contr_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_contr_neg

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
theorem _root_.solution (c : ℝ) (p q : PX m n) : contr c (p - q) = contr c p - contr c q := by
  rw [sub_eq_add_neg, contr_add, contr_neg]; ring
end PositivityTheory.Rg.Sw.LC.CoreC
