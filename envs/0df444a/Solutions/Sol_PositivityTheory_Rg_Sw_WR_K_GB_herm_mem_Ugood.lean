-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.herm_mem_Ugood
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:39.109843+00:00
-- url     : https://prove2.me/submissions/986125f0-17e8-4e33-b94f-03a77e1c9460

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBFinal
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_dP_eq

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) : herm y ∈ Ugood s := by
  obtain ⟨lam, -, -, h⟩ := dP_eq y
  have key : ∀ c : ℂ, (c = 1 ∨ c = -1) → ((1 : Mc n) + (c * (Complex.I * s)) • herm y).det ≠ 0 := by
    intro c hc
    rw [h, Finset.prod_ne_zero_iff]
    intro i _ h0
    have h1 := congrArg Complex.re h0
    rcases hc with rfl | rfl <;> rcases hs with rfl | rfl <;> simp at h1
  refine ⟨isUnit_iff_ne_zero.2 ?_, isUnit_iff_ne_zero.2 ?_⟩
  · have := key (-1) (Or.inr rfl); rwa [neg_one_mul, neg_smul, ← sub_eq_add_neg] at this
  · have := key 1 (Or.inl rfl); rwa [one_mul] at this
end PositivityTheory.Rg.Sw.WR.K.GB
