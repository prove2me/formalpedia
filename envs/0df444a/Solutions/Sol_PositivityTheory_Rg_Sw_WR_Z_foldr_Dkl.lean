-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.foldr_Dkl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:05:10.690784+00:00
-- url     : https://prove2.me/submissions/c45e3045-a40c-4328-9d68-c66f09d259ae

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_dirC_comp
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_herm_vkl

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Z
theorem _root_.solution (σ : Equiv.Perm (Fin n)) (U : Set (MC n)) (hU : IsOpen U) (hherm : ∀ y : E n, (herm y : MC n) ∈ U)
    (G : MC n → ℂ) (hG : AnalyticOnNhd ℂ G U) :
    ∀ L : List (Fin n), AnalyticOnNhd ℂ (L.foldr (fun k H => fun B => fderiv ℂ H B (eU (σ k) k)) G) U ∧
      L.foldr (fun k g => Dkl k (σ k) g) (fun y => G (herm y)) =
        fun y => (L.foldr (fun k H => fun B => fderiv ℂ H B (eU (σ k) k)) G) (herm y) := by
  intro L
  induction L with
  | nil => exact ⟨hG, rfl⟩
  | cons k L ih =>
    obtain ⟨ha, he⟩ := ih
    refine ⟨fun B hB => ((ContinuousLinearMap.apply ℂ ℂ (eU (σ k) k)).analyticAt _).comp
      ((ha.fderiv_of_isOpen hU) B hB), ?_⟩
    simp only [List.foldr_cons]
    rw [he]
    funext y
    unfold Dkl
    rw [dirC_comp _ y ((ha _ (hherm y)).differentiableAt), herm_vkl]
end PositivityTheory.Rg.Sw.WR.Z
