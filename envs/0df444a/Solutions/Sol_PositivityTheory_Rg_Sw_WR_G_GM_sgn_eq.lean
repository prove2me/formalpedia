-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GM.sgn_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:22.972372+00:00
-- url     : https://prove2.me/submissions/425f11a5-9626-4636-bd6e-f6b7fc31012c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
open PositivityTheory.Rg.Sw.WR.G.GM
namespace PositivityTheory.Rg.Sw.WR.G.GM
theorem _root_.solution (ε : Fin m → Bool) (a : Fin m) : sgn ε a = ((sR ε a : ℝ) : ℂ) := by
  unfold sgn sR; split_ifs <;> simp
end PositivityTheory.Rg.Sw.WR.G.GM
