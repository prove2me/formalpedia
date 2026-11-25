-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.DegLT.neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:43:44.020729+00:00
-- url     : https://prove2.me/submissions/487c040b-1bf6-482a-be5a-e405c194d819

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp

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
theorem _root_.solution {d : ℕ} {P : PX m n} (hP : DegLT d P) : DegLT d (-P) := by
  intro t ht; rw [MvPolynomial.support_neg] at ht; exact hP t ht
end DegLT
end PositivityTheory.Rg.Sw.LC.Basic
