-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.skodaLevi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:03:12.175292+00:00
-- url     : https://prove2.me/submissions/4ab0b637-d416-43a7-b63a-b808c4fd3e5a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_HlinVsqPos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SmoothRLog
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_vsq_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_smoothR_vsq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_db_eq_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_ck
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_db_comm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_finset_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_conj
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
private theorem db_log_eq_inv_mul_db {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (k : Fin n) (ph : M → ℝ) (hph : SmoothR n z ph) (hpos : ∀ y, 0 < ph y) (y : M) :
    db n z k (fun y => ((Real.log (ph y) : ℝ) : ℂ)) y =
      ((ph y : ℝ) : ℂ)⁻¹ * db n z k (fun y => ((ph y : ℝ) : ℂ)) y := by
  unfold db
  by_cases hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source
  · rw [dif_pos hex, dif_pos hex]
    have hs := Classical.choose_spec hex
    generalize Classical.choose hex = e at hs ⊢
    have hzy : z y = e y := hs.1 hs.2
    have hp : e y ∈ e.target := e.map_source hs.2
    have hsy : e.symm (e y) = y := e.left_inv hs.2
    have hc : ContDiffOn ℝ ∞ (fun w => ph (e.symm w)) e.target := by
      have h := Complex.reCLM.contDiff.comp_contDiffOn (hph e hs.1)
      simpa [Function.comp_def] using h
    have hd : DifferentiableAt ℝ (fun w => ph (e.symm w)) (e y) :=
      (hc.differentiableOn (by first | simp | exact WithTop.coe_le_coe.mpr le_top | norm_num)
        ).differentiableAt (e.open_target.mem_nhds hp)
    have hne : ph (e.symm (e y)) ≠ 0 := (hpos _).ne'
    have h1 := (Complex.ofRealCLM.hasFDerivAt.comp (e y) (hd.hasFDerivAt.log hne)).fderiv
    have h2 := (Complex.ofRealCLM.hasFDerivAt.comp (e y) hd.hasFDerivAt).fderiv
    have hf1 : (fun y => ((Real.log (ph y) : ℝ) : ℂ)) ∘ e.symm =
        ⇑Complex.ofRealCLM ∘ fun w => Real.log (ph (e.symm w)) := by
      funext w
      simp
    have hf2 : (fun y => ((ph y : ℝ) : ℂ)) ∘ e.symm =
        ⇑Complex.ofRealCLM ∘ fun w => ph (e.symm w) := by
      funext w
      simp
    rw [hzy]
    unfold wdb
    rw [hf1, hf2, h1, h2, hsy]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]
    ring
  · rw [dif_neg hex, dif_neg hex, mul_zero]
private theorem ofReal_vsq_perp_eq {p : ℕ} (g w : Fin p → ℂ) (hS : vsq g ≠ 0) :
    ((vsq (perp g w) : ℝ) : ℂ) = ∑ l, w l * (starRingEnd ℂ) (w l) -
      (∑ l, (starRingEnd ℂ) (g l) * w l) * (∑ l, g l * (starRingEnd ℂ) (w l)) / ((vsq g : ℝ) : ℂ) := by
  have hSc : ((vsq g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS
  have hgg : ∑ l, (starRingEnd ℂ) (g l) * g l = ((vsq g : ℝ) : ℂ) := by
    simp only [vsq, Complex.ofReal_sum, Complex.ofReal_pow, Complex.conj_mul']
  have e1 : ((vsq (perp g w) : ℝ) : ℂ) = ∑ l, (starRingEnd ℂ) (perp g w l) * perp g w l := by
    simp only [vsq, Complex.ofReal_sum, Complex.ofReal_pow, Complex.conj_mul']
  have e2 : ∀ l, (starRingEnd ℂ) (perp g w l) * perp g w l =
      w l * (starRingEnd ℂ) (w l) -
      ((∑ j, (starRingEnd ℂ) (g j) * w j) / ((vsq g : ℝ) : ℂ)) * (g l * (starRingEnd ℂ) (w l)) -
      ((∑ j, g j * (starRingEnd ℂ) (w j)) / ((vsq g : ℝ) : ℂ)) * ((starRingEnd ℂ) (g l) * w l) +
      ((∑ j, g j * (starRingEnd ℂ) (w j)) / ((vsq g : ℝ) : ℂ)) *
        ((∑ j, (starRingEnd ℂ) (g j) * w j) / ((vsq g : ℝ) : ℂ)) * ((starRingEnd ℂ) (g l) * g l) := by
    intro l
    simp only [perp, map_sub, map_mul, map_div₀, map_sum, Complex.conj_ofReal, Complex.conj_conj]
    ring
  rw [e1, Finset.sum_congr rfl (fun l _ => e2 l), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hgg]
  field_simp
  ring
private theorem levi_form_expand_eq_neg_sq_mul_add_sum {n p : ℕ} (a : Fin n → Fin p → ℂ) (G : Fin p → ℂ) (ξ : Fin n → ℂ)
    (c : ℂ) :
    ∑ j, ∑ k, (-(∑ l, (starRingEnd ℂ) (G l) * a j l) * c ^ 2 * (∑ l, (starRingEnd ℂ) (a k l) * G l) +
      c * ∑ l, (starRingEnd ℂ) (a k l) * a j l) * ξ j * (starRingEnd ℂ) (ξ k) =
    -(c ^ 2) * ((∑ l, (starRingEnd ℂ) (G l) * ∑ j, a j l * ξ j) *
      (∑ l, G l * (starRingEnd ℂ) (∑ j, a j l * ξ j))) +
    c * ∑ l, (∑ j, a j l * ξ j) * (starRingEnd ℂ) (∑ j, a j l * ξ j) := by
  have h1 : ∑ l, (starRingEnd ℂ) (G l) * ∑ j, a j l * ξ j =
      ∑ j, (∑ l, (starRingEnd ℂ) (G l) * a j l) * ξ j := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine (Finset.sum_comm).trans ?_
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have h2 : ∑ l, G l * (starRingEnd ℂ) (∑ j, a j l * ξ j) =
      ∑ k, (∑ l, (starRingEnd ℂ) (a k l) * G l) * (starRingEnd ℂ) (ξ k) := by
    simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    refine (Finset.sum_comm).trans ?_
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have h3 : ∑ l, (∑ j, a j l * ξ j) * (starRingEnd ℂ) (∑ j, a j l * ξ j) =
      ∑ j, ∑ k, (∑ l, (starRingEnd ℂ) (a k l) * a j l) * ξ j * (starRingEnd ℂ) (ξ k) := by
    simp only [map_sum, map_mul, Finset.sum_mul_sum]
    simp only [Finset.sum_mul]
    refine (Finset.sum_comm).trans ?_
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine (Finset.sum_comm).trans ?_
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  rw [h1, h2, h3, Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)
end ReciprocityTheory.L2DbarEstimates.H
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace ContDiff
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] :
    SkodaLeviStatement n M := by
  unfold SkodaLeviStatement
  intro z hz p g hg hg0 x ξ
  have hgs2 : ∀ l, Ck n z 2 (g l) := fun l => Smooth.ck n z 2 _ (Holo.smooth n z _ (hg l))
  have hgs : ∀ l, Ck n z 1 (g l) := fun l => Smooth.ck n z 1 _ (Holo.smooth n z _ (hg l))
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
  have hdbS : ∀ k y, db n z k (fun y => ((vsq (gv g y) : ℝ) : ℂ)) y =
      ∑ l, (starRingEnd ℂ) (d n z k (g l) y) * g l y := by
    intro k y
    rw [hSfun, db_finset_sum n z Finset.univ (fun l y => (starRingEnd ℂ) (g l y) * g l y)
      (fun l => Ck.mul n z 1 _ _ (hcg l) (hgs l)) k y]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [db_mul n z _ _ (hcg l) (hgs l) k y, db_conj, Holo.db_eq_zero n z _ (hg l) k y]
    ring
  have hdS : ∀ j, d n z j (fun y => ((vsq (gv g y) : ℝ) : ℂ)) x =
      ∑ l, (starRingEnd ℂ) (g l x) * d n z j (g l) x := by
    intro j
    rw [hSfun, d_finset_sum n z Finset.univ (fun l y => (starRingEnd ℂ) (g l y) * g l y)
      (fun l => Ck.mul n z 1 _ _ (hcg l) (hgs l)) j x]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [d_mul n z _ _ (hcg l) (hgs l) j x, d_conj, Holo.db_eq_zero n z _ (hg l) j x, map_zero]
    ring
  have hone : (fun y => ((vsq (gv g y) : ℝ) : ℂ) * (((vsq (gv g y) : ℝ) : ℂ))⁻¹) =
      fun _ => (1 : ℂ) := by
    funext y
    exact mul_inv_cancel₀ (hS y)
  have hdSi : ∀ j, d n z j (fun y => (((vsq (gv g y) : ℝ) : ℂ))⁻¹) x =
      -(d n z j (fun y => ((vsq (gv g y) : ℝ) : ℂ)) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2 := by
    intro j
    have h0 : d n z j (fun y => ((vsq (gv g y) : ℝ) : ℂ) * (((vsq (gv g y) : ℝ) : ℂ))⁻¹) x =
        0 := by
      rw [hone]
      exact d_const n z 1 j x
    exact eq_neg_mul_inv_sq_of_zero_eq _ _ _ (hS x) (h0.symm.trans (d_mul n z _ _ hSc hSi j x))
  have hE : ∀ k, Ck n z 1 (fun y => ∑ l, (starRingEnd ℂ) (d n z k (g l) y) * g l y) := by
    intro k
    have h : (fun y => ∑ l, (starRingEnd ℂ) (d n z k (g l) y) * g l y) =
        db n z k (fun y => ((vsq (gv g y) : ℝ) : ℂ)) := funext (fun y => (hdbS k y).symm)
    rw [h]
    exact Smooth.ck n z 1 _ (Smooth.db n z k _ hSsm)
  have hdg1 : ∀ k l, Ck n z 1 (d n z k (g l)) := fun k l => Ck.d n z 1 k (g l) (hgs2 l)
  have hdb0 : ∀ j l, db n z j (g l) = fun _ => 0 :=
    fun j l => funext (Holo.db_eq_zero n z _ (hg l) j)
  have hdEk : ∀ j k, d n z j (fun y => ∑ l, (starRingEnd ℂ) (d n z k (g l) y) * g l y) x =
      ∑ l, (starRingEnd ℂ) (d n z k (g l) x) * d n z j (g l) x := by
    intro j k
    rw [d_finset_sum n z Finset.univ (fun l y => (starRingEnd ℂ) (d n z k (g l) y) * g l y)
      (fun l => Ck.mul n z 1 _ _ (Ck.conj n z 1 _ (hdg1 k l)) (hgs l)) j x]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [d_mul n z _ _ (Ck.conj n z 1 _ (hdg1 k l)) (hgs l) j x, d_conj,
      ← d_db_comm n z (g l) (hgs2 l) k j x, hdb0 j l, d_const, map_zero]
    ring
  have hdE : ∀ j k, d n z j
      (fun y => (((vsq (gv g y) : ℝ) : ℂ))⁻¹ * ∑ l, (starRingEnd ℂ) (d n z k (g l) y) * g l y) x =
      -(∑ l, (starRingEnd ℂ) (g l x) * d n z j (g l) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2 *
        (∑ l, (starRingEnd ℂ) (d n z k (g l) x) * g l x) +
      ((vsq (gv g x) : ℝ) : ℂ)⁻¹ * ∑ l, (starRingEnd ℂ) (d n z k (g l) x) * d n z j (g l) x := by
    intro j k
    rw [d_mul n z _ _ hSi (hE k) j x, hdSi j, hdS j, hdEk j k]
    all_goals ring
  have hG : ∀ k, db n z k (fun y => ((Real.log (vsq (gv g y)) : ℝ) : ℂ)) =
      fun y => (((vsq (gv g y) : ℝ) : ℂ))⁻¹ * ∑ l, (starRingEnd ℂ) (d n z k (g l) y) * g l y := by
    intro k
    funext y
    rw [db_log_eq_inv_mul_db n z k _ (smoothR_vsq n z g hg) (fun y => vsq_pos _ (hg0 y)) y, hdbS k y]
  have hLevi : Levi n z (fun y => Real.log (vsq (gv g y))) x ξ =
      ∑ j, ∑ k, (-(∑ l, (starRingEnd ℂ) (g l x) * d n z j (g l) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2 *
        (∑ l, (starRingEnd ℂ) (d n z k (g l) x) * g l x) +
        ((vsq (gv g x) : ℝ) : ℂ)⁻¹ * ∑ l, (starRingEnd ℂ) (d n z k (g l) x) * d n z j (g l) x) * ξ j * (starRingEnd ℂ) (ξ k) := by
    unfold Levi
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [hG k, hdE j k]
  refine (hLevi.trans (levi_form_expand_eq_neg_sq_mul_add_sum (fun j l => d n z j (g l) x) (gv g x) ξ (((vsq (gv g x) : ℝ) : ℂ)⁻¹))).trans ?_
  rw [Complex.ofReal_div, ofReal_vsq_perp_eq (gv g x) (jacM n z g x ξ) (vsq_pos _ (hg0 x)).ne']
  simp only [jacM, gv]
  ring
end ReciprocityTheory.L2DbarEstimates.H
