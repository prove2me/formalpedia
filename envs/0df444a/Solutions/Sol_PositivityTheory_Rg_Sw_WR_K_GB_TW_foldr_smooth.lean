-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.TW.foldr_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:52:45.991887+00:00
-- url     : https://prove2.me/submissions/0393ef27-44de-4149-88cb-0e2b36b545e4

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_TD_smooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
open PositivityTheory.Rg.Sw.WR.K.GB.TW
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB.TW
theorem _root_.solution (f : Fin n → Fin n) : ∀ (l : List (Fin n)) (c : ℕ → E n → ℂ),
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j)) → ∀ j, ContDiff ℝ (⊤ : ℕ∞) ((l.foldr (fun k c' => TD k (f k) c') c) j)
  | [], c, hc => hc
  | a :: l, c, hc => TD_smooth (solution f l c hc) a (f a)
end PositivityTheory.Rg.Sw.WR.K.GB.TW
