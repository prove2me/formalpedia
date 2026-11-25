-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ap_dbar_cutExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:39:58.952613+00:00
-- url     : https://prove2.me/submissions/8bfa226f-d864-4bbd-9aee-828ba0db7aff

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_gt_local
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_cutExt_local
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_hasDerivAt_chi
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_db_eq_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_db_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_holo_jac
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_smoothR_ev
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_ckR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_ck
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_comp_real
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_mul


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
    (x : M) (hx : ev n g ph r x < m) (ξ : Fin n → ℂ) :
    dbarDot n z (cutExt n z g ph r c W χ ε) x ξ =
      ((deriv χ (ev n g ph r x / ε ^ 2) * (1 / ε ^ 2) : ℝ) : ℂ) * gt n z g c W x *
        dbarDot n z (fun y => (ev n g ph r y : ℂ)) x ξ := by
  have hev := ap_smoothR_ev n z g hg ph hph r
  have hloc := ap_cutExt_local n z g ph r c W m χ ε hS hW x hx
  have hgx := (ap_gt_local n z g ph r c W m hS hW x hx).self_of_nhds
  set C := ∑ p ∈ hS.toFinset, if x ∈ W p then c p else 0
  have hJ : Holo n z (fun y => C * jac n z g y) :=
    Holo.mul n z _ _ (Holo.const n z _) (ap_holo_jac n z g hg)
  have hk : SmoothR n z (fun y => χ (ev n g ph r y / ε ^ 2)) :=
    SmoothR.comp n z (fun t => χ (t / ε ^ 2)) (hχs.comp (contDiff_id.div_const _)) _ hev
  have hderiv : deriv (fun t => χ (t / ε ^ 2)) (ev n g ph r x) =
      deriv χ (ev n g ph r x / ε ^ 2) * (1 / ε ^ 2) := (ap_hasDerivAt_chi χ hχs ε _).deriv
  unfold dbarDot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [ap_db_congr n z hz j _ _ x hloc,
    db_mul n z _ _ (Smooth.ck n z 1 _ hk) (Smooth.ck n z 1 _ (Holo.smooth n z _ hJ)) j x,
    Holo.db_eq_zero n z _ hJ j x,
    db_comp_real n z (fun t => χ (t / ε ^ 2)) (hχs.comp (contDiff_id.div_const _)) _
      (SmoothR.ckR n z 1 _ hev) j x, hderiv, hgx]
  ring
end ReciprocityTheory.L2DbarEstimates.I
