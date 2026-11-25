-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.iterate_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:48.546825+00:00
-- url     : https://prove2.me/submissions/184714fe-4032-4cad-8d0f-7fad9c5b6a2e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBLink
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_deltaC_contDiffOn
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_delta_herm

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
variable {F G : Mc n → ℂ} {U : Set (Mc n)}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (hh : ∀ y, herm y ∈ U) (N : ℕ) :
    (Delta^[N] (fun y => F (herm y))) = (fun y => (DeltaC^[N] F) (herm y)) ∧
      ContDiffOn ℂ (⊤ : ℕ∞) (DeltaC^[N] F) U := by
  induction N with
  | zero => exact ⟨rfl, hF⟩
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih.1]
    exact ⟨delta_herm hU ih.2 hh, deltaC_contDiffOn hU ih.2⟩
end PositivityTheory.Rg.Sw.WR.K.GB
