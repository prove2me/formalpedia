-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.smoothReal_dbar_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:14:25.016271+00:00
-- url     : https://prove2.me/submissions/aa1198bf-368d-4685-b8fb-c8e6a3fb9654

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_DerivSmoothTransitionOfOneLt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : M → ℝ) (he : SmoothR n z e) : SmoothR n z (dbarSq n z (fun y => (e y : ℂ))) := by
  unfold SmoothR Smooth at *
  intro c hc
  have hG := he c hc
  have hfd : ContDiffOn ℝ ∞ (fun y => fderiv ℝ ((fun x => (e x : ℂ)) ∘ c.symm) y) c.target :=
    hG.fderiv_of_isOpen c.open_target (by simp)
  have hw : ∀ j, ContDiffOn ℝ ∞ (fun y => wdb n j ((fun x => (e x : ℂ)) ∘ c.symm) y) c.target := by
    intro j
    unfold wdb
    exact ((hfd.clm_apply contDiffOn_const).add
      (contDiffOn_const.mul (hfd.clm_apply contDiffOn_const))).div_const 2
  have hsum : ContDiffOn ℝ ∞
      (fun y => ∑ j ∈ Finset.univ, ‖wdb n j ((fun x => (e x : ℂ)) ∘ c.symm) y‖ ^ 2) c.target :=
    ContDiffOn.sum fun j _ => (contDiff_norm_sq ℝ).comp_contDiffOn (hw j)
  have hΦ := Complex.ofRealCLM.contDiff.comp_contDiffOn hsum
  refine hΦ.congr fun y hy => ?_
  simp only [Function.comp_apply, Complex.ofRealCLM_apply]
  congr 1
  unfold dbarSq
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  have hx : c.symm y ∈ c.source := c.map_target hy
  have hzx : z (c.symm y) = y := by rw [hc hx]; exact c.right_inv hy
  have hex : ∃ e' : OpenPartialHomeomorph M (V n), IsChart n z e' ∧ c.symm y ∈ e'.source :=
    ⟨c, hc, hx⟩
  unfold db
  rw [dif_pos hex]
  obtain ⟨hc1, hc2⟩ := Classical.choose_spec hex
  set c' := Classical.choose hex
  rw [hzx]
  have hcx : c' (c.symm y) = y := by rw [← hc1 hc2]; exact hzx
  have hsym : c'.symm y = c.symm y := by
    calc c'.symm y = c'.symm (c' (c.symm y)) := by rw [hcx]
      _ = c.symm y := c'.left_inv hc2
  have hyt : y ∈ c'.target := hcx ▸ c'.map_source hc2
  have hloc : (fun x => (e x : ℂ)) ∘ c'.symm =ᶠ[𝓝 y] (fun x => (e x : ℂ)) ∘ c.symm := by
    have h1 : ∀ᶠ w in 𝓝 y, w ∈ c'.target := c'.open_target.mem_nhds hyt
    have h2 : ∀ᶠ w in 𝓝 y, c'.symm w ∈ c.source :=
      (c'.continuousAt_symm hyt).preimage_mem_nhds (c.open_source.mem_nhds (by rw [hsym]; exact hx))
    filter_upwards [h1, h2] with w hw1 hw2
    have hcw : c (c'.symm w) = w := by
      rw [← hc hw2, hc1 (c'.map_target hw1), c'.right_inv hw1]
    have hsw : c'.symm w = c.symm w := by
      calc c'.symm w = c.symm (c (c'.symm w)) := (c.left_inv hw2).symm
        _ = c.symm w := by rw [hcw]
    simp only [Function.comp_apply, hsw]
  unfold wdb
  rw [hloc.fderiv_eq]
end ReciprocityTheory.L2DbarEstimates.F
