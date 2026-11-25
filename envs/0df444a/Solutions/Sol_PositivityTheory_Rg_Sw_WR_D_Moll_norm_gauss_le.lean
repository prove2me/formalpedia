-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.Moll.norm_gauss_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:51:01.376045+00:00
-- url     : https://prove2.me/submissions/d9a29229-2d46-479b-9a37-f16c68dad061

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollIdA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D PositivityTheory.Rg.Sw.WR.D.Moll
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D.Moll
theorem _root_.solution (ε : ℝ) (hε : 0 < ε) (y : E n) : ‖Complex.exp (-((ε * ip y y : ℝ) : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have h : 0 ≤ ip y y := by
    unfold ip
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => mul_self_nonneg _
  have : (-((ε * ip y y : ℝ) : ℂ)).re = -(ε * ip y y) := by simp
  rw [this, Real.exp_le_one_iff]
  nlinarith
end PositivityTheory.Rg.Sw.WR.D.Moll
