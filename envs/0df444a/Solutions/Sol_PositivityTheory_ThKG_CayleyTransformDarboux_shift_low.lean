-- Prove2me | solution 1 for PositivityTheory.ThKG.CayleyTransformDarboux.shift_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:19:12.065327+00:00
-- url     : https://prove2.me/submissions/e7e68644-aa13-4a67-9ee9-21026dd9c281

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ToralCohomology_ShiftLow
import Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_shift_eig

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
theorem _root_.solution {act : A →ₗ[ℂ] Module.End ℂ M} (h : Lie act) {H Z : A} {k : ℝ} (h0 : 0 < k)
    (hk : H * Z - Z * H = (-(k : ℂ)) • Z) {lam : ℂ} {V : Submodule ℂ M} (hV : V ≤ (act H).eigenspace lam) :
    ∀ x ∈ V ⊔ low (act H) lam, act Z x ∈ V ⊔ low (act H) lam := by
  have : V ⊔ low (act H) lam ≤ (V ⊔ low (act H) lam).comap (act Z) := by
    refine sup_le (fun x hx => ?_) (iSup_le fun t x hx => ?_)
    · refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem ⟨k, h0⟩ ?_)
      have := shift_eig h hk (hV hx)
      rwa [← sub_eq_add_neg] at this
    · refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem ⟨t.1 + k, add_pos t.2 h0⟩ ?_)
      have := shift_eig h hk hx
      convert this using 2
      push_cast; ring
  exact fun x hx => this hx
end PositivityTheory.ThKG.CayleyTransformDarboux
