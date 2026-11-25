-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.TW.TDelta_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:50.750803+00:00
-- url     : https://prove2.me/submissions/f2587987-f502-452a-8499-7d575ab57de1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_foldr_supp

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
theorem _root_.solution {c : ℕ → E n → ℂ} {M : ℕ} (hM : ∀ j, M ≤ j → c j = 0) :
    ∀ j, M + n ≤ j → TDelta c j = 0 := by
  intro j hj
  funext y
  simp only [TDelta, Pi.zero_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [foldr_supp σ (List.finRange n) c M hM j (by simpa using hj)]
  simp
end PositivityTheory.Rg.Sw.WR.K.GB.TW
