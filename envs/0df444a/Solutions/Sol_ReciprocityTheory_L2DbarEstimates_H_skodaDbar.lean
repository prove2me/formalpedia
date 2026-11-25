-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.skodaDbar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:57:52.096802+00:00
-- url     : https://prove2.me/submissions/dff6114b-cb71-4f87-bc3c-c2366f03f66b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_HlinVsqPos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SmoothRLog
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_vsq_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_smoothR_vsq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_db_eq_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_ck
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_finset_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace ContDiff
private theorem eq_neg_mul_inv_sq_of_zero_eq (A B s : ℂ) (hs : s ≠ 0) (h : 0 = A * s⁻¹ + s * B) :
    B = -A * s⁻¹ ^ 2 := by
  have hinv : s⁻¹ * s = 1 := inv_mul_cancel₀ hs
  linear_combination (-(s⁻¹)) * h - B * hinv
end ReciprocityTheory.L2DbarEstimates.H
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace ContDiff
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] :
    SkodaDbarStatement n M := by
  unfold SkodaDbarStatement
  intro z hz p g u hg hu hg0 x i ξ
  have hgs : ∀ l, Ck n z 1 (g l) := fun l => Smooth.ck n z 1 _ (Holo.smooth n z _ (hg l))
  have hus : Ck n z 1 u := Smooth.ck n z 1 _ (Holo.smooth n z _ hu)
  have hcg : ∀ l, Ck n z 1 (fun y => (starRingEnd ℂ) (g l y)) :=
    fun l => Ck.conj n z 1 _ (hgs l)
  have hS : ∀ y, ((vsq (gv g y) : ℝ) : ℂ) ≠ 0 :=
    fun y => Complex.ofReal_ne_zero.mpr (vsq_pos _ (hg0 y)).ne'
  have hSsm : Smooth n z (fun y => ((vsq (gv g y) : ℝ) : ℂ)) := smoothR_vsq n z g hg
  have hSc : Ck n z 1 (fun y => ((vsq (gv g y) : ℝ) : ℂ)) := Smooth.ck n z 1 _ hSsm
  have hSi : Ck n z 1 (fun y => (((vsq (gv g y) : ℝ) : ℂ))⁻¹) := by
    apply Smooth.ck
    unfold Smooth
    intro e he
    exact (hSsm e he).inv (fun y _ => hS _)
  have hSfun : (fun y => ((vsq (gv g y) : ℝ) : ℂ)) =
      fun y => ∑ l, (starRingEnd ℂ) (g l y) * g l y := by
    funext y
    simp only [vsq, gv, Complex.ofReal_sum, Complex.ofReal_pow, Complex.conj_mul']
  have hdbS : ∀ j, db n z j (fun y => ((vsq (gv g y) : ℝ) : ℂ)) x =
      ∑ l, (starRingEnd ℂ) (d n z j (g l) x) * g l x := by
    intro j
    rw [hSfun, db_finset_sum n z Finset.univ (fun l y => (starRingEnd ℂ) (g l y) * g l y)
      (fun l => Ck.mul n z 1 _ _ (hcg l) (hgs l)) j x]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [db_mul n z _ _ (hcg l) (hgs l) j x, db_conj, Holo.db_eq_zero n z _ (hg l) j x]
    ring
  have hone : (fun y => ((vsq (gv g y) : ℝ) : ℂ) * (((vsq (gv g y) : ℝ) : ℂ))⁻¹) =
      fun _ => (1 : ℂ) := by
    funext y
    exact mul_inv_cancel₀ (hS y)
  have hdbSi : ∀ j, db n z j (fun y => (((vsq (gv g y) : ℝ) : ℂ))⁻¹) x =
      -(db n z j (fun y => ((vsq (gv g y) : ℝ) : ℂ)) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2 := by
    intro j
    have h0 : db n z j (fun y => ((vsq (gv g y) : ℝ) : ℂ) * (((vsq (gv g y) : ℝ) : ℂ))⁻¹) x =
        0 := by
      rw [hone]
      exact db_const n z 1 j x
    exact eq_neg_mul_inv_sq_of_zero_eq _ _ _ (hS x) (h0.symm.trans (db_mul n z _ _ hSc hSi j x))
  have hF : (fun y => u y * (starRingEnd ℂ) (g i y) / ((vsq (gv g y) : ℝ) : ℂ)) =
      fun y => u y * ((starRingEnd ℂ) (g i y) * (((vsq (gv g y) : ℝ) : ℂ))⁻¹) := by
    funext y
    rw [div_eq_mul_inv, mul_assoc]
  have hdbF : ∀ j, db n z j
      (fun y => u y * (starRingEnd ℂ) (g i y) / ((vsq (gv g y) : ℝ) : ℂ)) x =
      u x * ((starRingEnd ℂ) (d n z j (g i) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ + (starRingEnd ℂ) (g i x) *
        (-(∑ l, (starRingEnd ℂ) (d n z j (g l) x) * g l x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2)) := by
    intro j
    rw [hF, db_mul n z _ _ hus (Ck.mul n z 1 _ _ (hcg i) hSi) j x, Holo.db_eq_zero n z _ hu j x,
      db_mul n z _ _ (hcg i) hSi j x, db_conj, hdbSi j, hdbS j]
    try beta_reduce
    ring
  have hL : dbarDot n z (fun y => u y * (starRingEnd ℂ) (g i y) / ((vsq (gv g y) : ℝ) : ℂ)) x ξ =
      ∑ j, u x * ((starRingEnd ℂ) (d n z j (g i) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ + (starRingEnd ℂ) (g i x) *
        (-(∑ l, (starRingEnd ℂ) (d n z j (g l) x) * g l x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2)) *
        (starRingEnd ℂ) (ξ j) := by
    unfold dbarDot
    exact Finset.sum_congr rfl (fun j _ => by rw [hdbF j])
  have hsplit : ∑ j, u x * ((starRingEnd ℂ) (d n z j (g i) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ + (starRingEnd ℂ) (g i x) *
        (-(∑ l, (starRingEnd ℂ) (d n z j (g l) x) * g l x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2)) *
        (starRingEnd ℂ) (ξ j) =
      u x * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ * ∑ j, (starRingEnd ℂ) (d n z j (g i) x) * (starRingEnd ℂ) (ξ j) -
        u x * (starRingEnd ℂ) (g i x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2 *
          ∑ j, (∑ l, (starRingEnd ℂ) (d n z j (g l) x) * g l x) * (starRingEnd ℂ) (ξ j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hswap : ∑ j, (∑ l, (starRingEnd ℂ) (d n z j (g l) x) * g l x) * (starRingEnd ℂ) (ξ j) =
      ∑ l, g l x * ∑ j, (starRingEnd ℂ) (d n z j (g l) x) * (starRingEnd ℂ) (ξ j) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have hconj : (starRingEnd ℂ) (perp (gv g x) (jacM n z g x ξ) i) =
      ∑ j, (starRingEnd ℂ) (d n z j (g i) x) * (starRingEnd ℂ) (ξ j) -
        (starRingEnd ℂ) (g i x) *
          (∑ l, g l x * ∑ j, (starRingEnd ℂ) (d n z j (g l) x) * (starRingEnd ℂ) (ξ j)) /
            ((vsq (gv g x) : ℝ) : ℂ) := by
    simp only [perp, jacM, gv, map_sub, map_mul, map_sum, map_div₀, Complex.conj_ofReal,
      Complex.conj_conj]
    ring
  rw [hL, hsplit, hswap, hconj]
  ring
end ReciprocityTheory.L2DbarEstimates.H
