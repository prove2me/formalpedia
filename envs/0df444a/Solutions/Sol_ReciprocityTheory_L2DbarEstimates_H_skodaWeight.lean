-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.skodaWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:10:52.357892+00:00
-- url     : https://prove2.me/submissions/a52eebe2-46d6-44fc-90af-d8ce67efeb35

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_HlinVsqPos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SmoothRLog
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_vsq_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_smoothR_vsq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_smoothR_log
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_skodaLevi
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_ckR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_levi_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_levi_const_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace ContDiff
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] :
    SkodaWeightStatement n M := by
  unfold SkodaWeightStatement
  intro z hz p g φ₀ t hg hg0 hφ hL ht
  have hpos : ∀ x, 0 < vsq (gv g x) := fun x => vsq_pos _ (hg0 x)
  have hlog : SmoothR n z (fun x => Real.log (vsq (gv g x))) :=
    smoothR_log n z _ (smoothR_vsq n z g hg) hpos
  have hconst : SmoothR n z (fun _ : M => t) := by
    unfold SmoothR Smooth
    intro e _
    exact contDiffOn_const
  have htl : SmoothR n z (fun x => t * Real.log (vsq (gv g x))) :=
    SmoothR.mul n z _ _ hconst hlog
  have hsm : SmoothR n z (skW g φ₀ t) := SmoothR.add n z _ _ hφ htl
  have hlevi : ∀ x ξ, Levi n z (skW g φ₀ t) x ξ = Levi n z φ₀ x ξ +
      (t : ℂ) * ((vsq (perp (gv g x) (jacM n z g x ξ)) / vsq (gv g x) : ℝ) : ℂ) := by
    intro x ξ
    have e1 := levi_add n z φ₀ (fun y => t * Real.log (vsq (gv g y)))
      (SmoothR.ckR n z 2 φ₀ hφ) (SmoothR.ckR n z 2 _ htl) x ξ
    have e2 := levi_const_mul n z t (fun y => Real.log (vsq (gv g y)))
      (SmoothR.ckR n z 2 _ hlog) x ξ
    have e3 := skodaLevi n M z hz p g hg hg0 x ξ
    rw [← e3, ← e2]
    exact e1
  have hre : ∀ x ξ, (Levi n z (skW g φ₀ t) x ξ).re =
      (Levi n z φ₀ x ξ).re + t * (vsq (perp (gv g x) (jacM n z g x ξ)) / vsq (gv g x)) := by
    intro x ξ
    rw [hlevi x ξ, Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
  have hq : ∀ x ξ, 0 ≤ t * (vsq (perp (gv g x) (jacM n z g x ξ)) / vsq (gv g x)) := by
    intro x ξ
    have h0 : 0 ≤ vsq (perp (gv g x) (jacM n z g x ξ)) := by
      unfold vsq
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    exact mul_nonneg ht (div_nonneg h0 (hpos x).le)
  refine ⟨hsm, ?_, ?_⟩
  · unfold LeviNonneg
    intro x ξ
    rw [hre]
    exact add_nonneg (hL x ξ) (hq x ξ)
  · intro x ξ
    rw [hre]
    linarith [hL x ξ]
end ReciprocityTheory.L2DbarEstimates.H
