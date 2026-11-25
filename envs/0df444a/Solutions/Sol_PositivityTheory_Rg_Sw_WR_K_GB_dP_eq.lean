-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.dP_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:16.332043+00:00
-- url     : https://prove2.me/submissions/8f909e4f-044a-40b5-bf2d-e3df4afd81e2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBFinal
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_det_one_add_herm

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
theorem _root_.solution (y : E n) : ∃ lam : Fin n → ℝ, dP y = ∏ i, (1 + lam i ^ 2) ∧
    (((dP y : ℝ) : ℂ) = ((1 : Mc n) + herm y * herm y).det) ∧
    ∀ c : ℂ, ((1 : Mc n) + c • herm y).det = ∏ i, (1 + c * lam i) := by
  obtain ⟨lam, h⟩ := det_one_add_herm y
  have h2 := (h 0).2
  have hre : dP y = ∏ i, (1 + lam i ^ 2) := by
    simp only [dP, h2]
    rw [show (∏ i, (1 + (lam i : ℂ) ^ 2)) = ((∏ i, (1 + lam i ^ 2) : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
  refine ⟨lam, hre, ?_, fun c => (h c).1⟩
  rw [hre, h2]; push_cast; rfl
end PositivityTheory.Rg.Sw.WR.K.GB
