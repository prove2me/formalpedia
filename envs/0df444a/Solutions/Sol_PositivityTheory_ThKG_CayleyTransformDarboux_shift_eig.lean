-- Prove2me | solution 1 for PositivityTheory.ThKG.CayleyTransformDarboux.shift_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:09:46.485347+00:00
-- url     : https://prove2.me/submissions/5322e5b7-9101-4736-bde9-14bef7a11dfe

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ToralCohomology_ShiftLow
import Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_Lie_comm

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
variable {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.ThKG.CayleyTransformDarboux
theorem _root_.solution {act : A →ₗ[ℂ] Module.End ℂ M} (h : Lie act) {H Z : A} {k : ℂ} (hk : H * Z - Z * H = k • Z) {mu : ℂ} {x : M}
    (hx : x ∈ (act H).eigenspace mu) : act Z x ∈ (act H).eigenspace (mu + k) := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  rw [h.comm, hx, hk, map_smul, map_smul, LinearMap.smul_apply, add_smul]
end PositivityTheory.ThKG.CayleyTransformDarboux
