-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.mom_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:21.961843+00:00
-- url     : https://prove2.me/submissions/36c51db3-4dc0-4922-a570-9e6e20e94e5e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_OneMom
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableMonomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_flip_flip
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_integrable_evX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LC.flip_flip

set_option autoImplicit false
noncomputable section
open MvPolynomial MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
variable (hM : OneMom)
include hM
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution (c : ℝ) (hc : 0 < c) (P Q : PX m n) : mom c (P + Q) = mom c P + mom c Q := by
  rw [mom, mom, mom, ← integral_add (integrable_evX hM c hc P) (integrable_evX hM c hc Q)]
  congr 1; funext x; simp [evX, add_mul]
end PositivityTheory.Rg.Sw.LC
