-- Prove2me | solution 1 for PositivityTheory.ThKG.CayleyTransformDarboux.dg_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:35:44.965088+00:00
-- url     : https://prove2.me/submissions/584bf75d-e6c8-476f-82ae-2b3df13de425

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ToralCohomology_ShiftLow
import Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_dg_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action PositivityTheory.KReal
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.CayleyTransformDarboux
variable {ι I M : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.ThKG.CayleyTransformDarboux
theorem _root_.solution {act : (ι → Matrix I I ℂ) →ₗ[ℂ] Module.End ℂ M} (h : I → ℝ) {Λ : ι → I → ℂ} {f : M}
    (hf : ∀ w a, act (un w a a) f = Λ w a • f) : f ∈ (act (dg ι h)).eigenspace (∑ w, ∑ a, h a * Λ w a) := by
  rw [Module.End.mem_eigenspace_iff, dg_eq]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hf, Finset.sum_smul, smul_smul]
end PositivityTheory.ThKG.CayleyTransformDarboux
