-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.tl_levi_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:54:43.869501+00:00
-- url     : https://prove2.me/submissions/b121ddd0-1b53-4459-9603-8705913f490d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwistLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tlK_contDiff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tl_deriv_k
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tl_lw_le
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tl_lw_smoothR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tl_twist_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_ckR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_levi_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_levi_const_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_smoothR_const


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
open scoped ENNReal ContDiff
noncomputable section
open Filter Topology
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (hCh : ChainStatement n M)
    (z : M → V n) (g : Fin n → M → ℂ) (ph ph2 : M → ℝ) (r : ℝ) (j : ℕ) (ε δ : ℝ)
    (hz : IsLocalHomeomorph z) (hg : ∀ i, Holo n z (g i)) (hph : SmoothR n z ph)
    (hph2 : SmoothR n z ph2) (hr : 0 < r) (hε : 0 < ε) (hδ : 0 < δ)
    (hbd : ∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) (x : M) (ξ : Fin n → ℂ) :
    (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re =
      (Levi n z ph2 x ξ).re + ((n : ℝ) + j) * (Levi n z ph x ξ).re +
        (n : ℝ) * (Levi n z (lw n g ph r δ) x ξ).re +
        tlKp (1 + Real.log (1 + ε ^ 2)) (lw n g ph r ε x) * (Levi n z (lw n g ph r ε) x ξ).re +
        tlKpp (1 + Real.log (1 + ε ^ 2)) (lw n g ph r ε x) *
          ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ ^ 2 := by
  set c := 1 + Real.log (1 + ε ^ 2) with hc
  have hlε := tl_lw_smoothR n z g ph r ε hg hph hε
  have hlδ := tl_lw_smoothR n z g ph r δ hg hph hδ
  have hA : SmoothR n z (fun y => ph2 y + ((n : ℝ) + j) * ph y) :=
    SmoothR.add n z _ _ hph2 (SmoothR.mul n z _ _ (smoothR_const n z _) hph)
  have hBB : SmoothR n z (fun y => (n : ℝ) * lw n g ph r δ y) :=
    SmoothR.mul n z _ _ (smoothR_const n z _) hlδ
  have hwgt : SmoothR n z (wgt n g ph ph2 r j δ) := SmoothR.add n z _ _ hA hBB
  have htw_eq := tl_twist_eq n g ph r ε hr hε hbd
  have htw : SmoothR n z (twist n g ph r ε) := by
    rw [htw_eq]; exact SmoothR.comp n z _ (tlK_contDiff c) _ hlε
  have e1 : Levi n z (wgt n g ph ph2 r j δ) x ξ =
      Levi n z ph2 x ξ + (((n : ℝ) + j : ℝ) : ℂ) * Levi n z ph x ξ +
        ((n : ℝ) : ℂ) * Levi n z (lw n g ph r δ) x ξ := by
    have h1 := levi_add n z _ _ (SmoothR.ckR n z 2 _ hA) (SmoothR.ckR n z 2 _ hBB) x ξ
    have h2 := levi_add n z _ _ (SmoothR.ckR n z 2 _ hph2)
      (SmoothR.ckR n z 2 _ (SmoothR.mul n z _ _ (smoothR_const n z ((n : ℝ) + j)) hph)) x ξ
    have h3 := levi_const_mul n z ((n : ℝ) + j) ph (SmoothR.ckR n z 2 _ hph) x ξ
    have h4 := levi_const_mul n z (n : ℝ) _ (SmoothR.ckR n z 2 _ hlδ) x ξ
    change Levi n z (fun y => ph2 y + ((n : ℝ) + j) * ph y + (n : ℝ) * lw n g ph r δ y) x ξ = _
    rw [h1, h2, h3, h4]
  have hk : ContDiff ℝ 2 (tlK c) := contDiff_infty.1 (tlK_contDiff c) 2
  have e2 : Levi n z (twist n g ph r ε) x ξ =
      ((tlKp c (lw n g ph r ε x) : ℝ) : ℂ) * Levi n z (lw n g ph r ε) x ξ +
        ((tlKpp c (lw n g ph r ε x) : ℝ) : ℂ) *
          ((‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [htw_eq, hCh z hz (tlK c) (lw n g ph r ε) hk hlε x ξ]
    obtain ⟨d1, d2⟩ := tl_deriv_k c (lw n g ph r ε x) (by linarith [tl_lw_le n g ph r ε hr hε hbd x])
    rw [d1, d2]
  rw [levi_add n z _ _ (SmoothR.ckR n z 2 _ hwgt) (SmoothR.ckR n z 2 _ htw) x ξ, e1, e2]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
  ring
end ReciprocityTheory.L2DbarEstimates.I
