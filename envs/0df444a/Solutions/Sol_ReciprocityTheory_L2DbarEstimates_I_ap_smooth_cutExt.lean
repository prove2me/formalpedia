-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ap_smooth_cutExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:39:19.067594+00:00
-- url     : https://prove2.me/submissions/aa89e4ff-1ab5-448f-a4a1-b62eb3aaaa99

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_cutExt_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_cutExt_local
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_cont_of_smoothR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_holo_jac
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_smoothR_ev
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_smooth_of_local
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff Classical
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph : M → ℝ)
    (hph : SmoothR n z ph) (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ) (χ : ℝ → ℝ) (ε : ℝ)
    (hS : (zeroSet n g).Finite) (hW : IsLocalData n g ph r W m) (hχs : ContDiff ℝ ∞ χ)
    (hχ0 : ∀ t, 1 ≤ t → χ t = 0) (hε : 0 < ε) (hm : ε ^ 2 < m) :
    Smooth n z (cutExt n z g ph r c W χ ε) := by
  have hev := ap_smoothR_ev n z g hg ph hph r
  have hcont := ap_cont_of_smoothR n z hz _ hev
  apply ap_smooth_of_local
  intro x
  by_cases hx : ev n g ph r x < m
  · refine ⟨_, ?_, ap_cutExt_local n z g ph r c W m χ ε hS hW x hx⟩
    have hk : SmoothR n z (fun y => χ (ev n g ph r y / ε ^ 2)) :=
      SmoothR.comp n z (fun t => χ (t / ε ^ 2)) (hχs.comp (contDiff_id.div_const _)) _ hev
    exact Smooth.mul n z _ _ hk (Holo.smooth n z _ (Holo.mul n z _ _ (Holo.const n z _)
      (ap_holo_jac n z g hg)))
  · exact ⟨fun _ => 0, Smooth.const n z 0,
      ap_cutExt_zero n z g ph r c W χ ε hcont hχ0 hε x (by linarith [not_lt.1 hx])⟩
end ReciprocityTheory.L2DbarEstimates.I
