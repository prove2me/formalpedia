-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Ib.contDiff_dkl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:03.225963+00:00
-- url     : https://prove2.me/submissions/7740d20b-e25a-4907-99d1-c16ac7df6209

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Ib
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Ib
theorem _root_.solution {g : E n → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (k l : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (Dkl k l g) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ g) := (contDiff_infty_iff_fderiv.mp hg).2
  simp only [Dkl, dirC]
  exact (hd.clm_apply contDiff_const).add (contDiff_const.mul (hd.clm_apply contDiff_const))
end PositivityTheory.Rg.Sw.WR.Ib
