-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.DegLT.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:51:37.84064+00:00
-- url     : https://prove2.me/submissions/06987117-6947-442e-81fd-0cc802010f78

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_DegLT_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_DegLT_neg

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Basic
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.Basic
namespace DegLT
theorem _root_.solution {d : ℕ} {P Q : PX m n} (hP : DegLT d P) (hQ : DegLT d Q) : DegLT d (P - Q) := by
  rw [sub_eq_add_neg]; exact hP.add hQ.neg
end DegLT
end PositivityTheory.Rg.Sw.LC.Basic
