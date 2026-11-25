-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_LC_fock_add___b68a5475b7b1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:49:51.251028+00:00
-- url     : https://prove2.me/submissions/17b7513d-f96d-408a-9e59-481814ea7c28

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HopPderivComm

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
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
variable (hB : FockBasic)
include hB
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution {c : ℝ} (hc : 0 < c) (p q : PX m n) : fock c (p + q) = fock c p + fock c q :=
  (hB m n c hc).1.map_add p q
end PositivityTheory.Rg.Sw.LC
