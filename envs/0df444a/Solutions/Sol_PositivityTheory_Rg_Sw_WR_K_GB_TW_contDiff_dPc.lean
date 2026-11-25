-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.TW.contDiff_dPc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:17:53.155802+00:00
-- url     : https://prove2.me/submissions/3f1428f4-2c1c-41ea-996f-c4d666cf7412

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_contDiff_herm_entry

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
theorem _root_.solution : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => (1 + herm y * herm y).det) := by
  have hM : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => (1 + herm y * herm y) i j) := by
    intro i j
    simp only [Matrix.add_apply, Matrix.mul_apply]
    exact contDiff_const.add (ContDiff.sum fun k _ => (contDiff_herm_entry i k).mul (contDiff_herm_entry k j))
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM (σ i) i)
end PositivityTheory.Rg.Sw.WR.K.GB.TW
