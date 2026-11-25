-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.localize
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:19:47.131854+00:00
-- url     : https://prove2.me/submissions/22cb00f9-2532-418d-993e-99bb05f58056

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Localize
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_aemeasurable_unweighted_two_form
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_aem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_ck_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_d_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_d_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_db_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_db_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_lintegral_sum_lt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_norm_sum_sq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_ofReal_le
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_piece
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_sum_apply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_weaklyLocallyCompact
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_two_form_norm_sq_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_two_form_sq_finset_sum_le
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_ckR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart_partition


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
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hMD : MultDivStatement n M) (hMS : MultSStatement n M) :
    LocalizeStatement n M := by
  intro z hz H G D S hG hD hS hGD hGS hcG hcD hcS
  have := loc_weaklyLocallyCompact n z hz
  have hK : IsCompact (tsupport G ∪ tsupport D ∪ tsupport S) := (hcG.union hcD).union hcS
  set K := tsupport G ∪ tsupport D ∪ tsupport S with hKdef
  obtain ⟨K', hK', hKK'⟩ := exists_compact_superset hK
  obtain ⟨N, e, χ, he, hχs, hχc, hχsub, -, -, hχK⟩ :=
    exists_chart_partition n z hz K' univ hK' isOpen_univ (subset_univ _)
  have hck : ∀ i, Ck n z 1 (fun y => (χ i y : ℂ)) := fun i => SmoothR.ckR n z 1 (χ i) (hχs i)
  have hoff : ∀ x, x ∉ K → G x = 0 ∧ D x = 0 ∧ S x = 0 := fun x hx =>
    ⟨image_eq_zero_of_notMem_tsupport fun h => hx (Or.inl (Or.inl h)),
     image_eq_zero_of_notMem_tsupport fun h => hx (Or.inl (Or.inr h)),
     image_eq_zero_of_notMem_tsupport fun h => hx (Or.inr h)⟩
  have hone : ∀ x ∈ K, ∑ i, (χ i x : ℂ) = 1 := fun x hx => by
    rw [← Complex.ofReal_sum, hχK x (interior_subset (hKK' hx)), Complex.ofReal_one]
  have hev : ∀ x ∈ K, (fun y => ∑ i, (χ i y : ℂ)) =ᶠ[𝓝 x] fun _ => (1 : ℂ) := fun x hx => by
    filter_upwards [isOpen_interior.mem_nhds (hKK' hx)] with y hy
    rw [← Complex.ofReal_sum, hχK y (interior_subset hy), Complex.ofReal_one]
  have hdz : ∀ x ∈ K, ∀ j, ∑ i, d n z j (fun y => (χ i y : ℂ)) x = 0 := fun x hx j => by
    rw [← loc_d_sum n z Finset.univ _ hck j x, loc_d_congr n z hz j _ _ x (hev x hx), d_const]
  have hdbz : ∀ x ∈ K, ∀ j, ∑ i, db n z j (fun y => (χ i y : ℂ)) x = 0 := fun x hx j => by
    rw [← loc_db_sum n z Finset.univ _ hck j x, loc_db_congr n z hz j _ _ x (hev x hx), db_const]
  have sG : ∀ x, G x = ∑ i, locG (χ i) G x := fun x => by
    by_cases hx : x ∈ K
    · simp only [locG]; rw [← Finset.sum_smul, hone x hx, one_smul]
    · simp [locG, (hoff x hx).1]
  have sD : ∀ x, D x = ∑ i, locD n z (χ i) G D x := fun x => by
    by_cases hx : x ∈ K
    · simp only [locD, Finset.sum_add_distrib, ← Finset.sum_mul, hone x hx, one_mul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, hdz x hx, zero_mul, Finset.sum_const_zero, add_zero]
    · simp [locD, (hoff x hx).1, (hoff x hx).2.1]
  have sS : ∀ x j k, S x j k = ∑ i, locS n z (χ i) G S x j k := fun x j k => by
    by_cases hx : x ∈ K
    · simp only [locS, wedge, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        hone x hx, one_mul, hdbz x hx, zero_mul, sub_self, add_zero]
    · simp [locS, wedge, (hoff x hx).1, (hoff x hx).2.2]
  have hP := fun i => loc_piece n z hz hMD hMS (χ i) (hχs i) (hχc i) (e i).source
    ((hχsub i).trans inter_subset_left) G D S hG hD hS hGD hGS
  choose K0 hK0 happ using fun i => H (e i) _ _ _ (he i) (hP i).1 (hP i).2.1 (hP i).2.2.1
    (hP i).2.2.2.1 (hP i).2.2.2.2.1 (hP i).2.2.2.2.2.1 (hP i).2.2.2.2.2.2.1
    (hP i).2.2.2.2.2.2.2.1 (hP i).2.2.2.2.2.2.2.2.1 (hP i).2.2.2.2.2.2.2.2.2.1
    (hP i).2.2.2.2.2.2.2.2.2.2
  refine ⟨⋃ i, K0 i, isCompact_iUnion hK0, fun δ hδ => ?_⟩
  obtain ⟨δ', hδ'0, hδ'⟩ := ENNReal.exists_pos_mul_lt (a := (N : ℝ≥0∞) * N) (b := δ)
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) (ENNReal.natCast_ne_top N)) hδ.ne'
  choose g hgT hg0 hg1 hg2 hg3 using fun i => happ i δ' hδ'0
  have hgc : ∀ i j, Ck n z 2 (fun x => g i x j) := fun i j => (hgT i j).1
  have hgc1 : ∀ i j, Ck n z (0 + 1) (fun x => g i x j) := fun i j =>
    Ck.mono n z 1 2 (by norm_num) _ (hgc i j)
  have hfun : ∀ j, (fun x => (∑ i, g i x) j) = fun x => ∑ i, g i x j := fun j =>
    funext fun x => loc_sum_apply _ j
  have hvan : ∀ x, x ∉ ⋃ i, K0 i → ∑ i, g i x = 0 := fun x hx =>
    Finset.sum_eq_zero fun i _ => hg0 i x fun h => hx (mem_iUnion.2 ⟨i, h⟩)
  have hgcont : ∀ i, Continuous (g i) := fun i => by
    have : Continuous (fun x => WithLp.toLp 2 (fun j => g i x j)) :=
      (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => Ck.continuous n z hz 2 _ (hgc i j))
    exact this
  have hdivc : ∀ i, Continuous (divF n z (g i)) := fun i => by
    unfold divF
    exact continuous_finsetSum _ fun j _ => Ck.continuous n z hz 0 _ (Ck.d n z 0 j _ (hgc1 i j))
  have hsbc : ∀ i, Continuous (sbar n z (g i)) := fun i => by
    unfold sbar
    exact continuous_pi fun j => continuous_pi fun k =>
      (Ck.continuous n z hz 0 _ (Ck.db n z 0 j _ (hgc1 i k))).sub
        (Ck.continuous n z hz 0 _ (Ck.db n z 0 k _ (hgc1 i j)))
  have hdiv : ∀ x, divF n z (fun x => ∑ i, g i x) x = ∑ i, divF n z (g i) x := fun x => by
    simp only [divF]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfun j, loc_d_sum n z Finset.univ (fun i y => g i y j) (fun i => hgc1 i j) j x]
  have hsb : ∀ x j k, sbar n z (fun x => ∑ i, g i x) x j k = ∑ i, sbar n z (g i) x j k :=
    fun x j k => by
    simp only [sbar]
    rw [hfun k, hfun j, loc_db_sum n z _ (fun i y => g i y k) (fun i => hgc1 i k) j x,
      loc_db_sum n z _ (fun i y => g i y j) (fun i => hgc1 i j) k x, Finset.sum_sub_distrib]
  refine ⟨fun x => ∑ i, g i x, fun j => ⟨?_, ?_⟩, hvan, ?_, ?_, ?_⟩
  · rw [hfun j]; exact loc_ck_sum n z 2 _ _ fun i => hgc i j
  · refine HasCompactSupport.intro (isCompact_iUnion hK0) fun x hx => ?_
    show (∑ i, g i x) j = 0
    rw [hvan x hx]; rfl
  · unfold nV
    refine loc_lintegral_sum_lt (vol n z) _ (fun i x => ENNReal.ofReal (‖g i x - locG (χ i) G x‖ ^ 2 *
      Real.exp (-(fun _ : M => (0 : ℝ)) x))) (fun i => loc_aem _ _ ((hgcont i).aestronglyMeasurable.sub
      (hP i).1.1)) (fun x => ?_) δ' δ (fun i => hg1 i) hδ'
    simp only [neg_zero, Real.exp_zero, mul_one]
    have : (∑ i, g i x) - G x = ∑ i, (g i x - locG (χ i) G x) := by
      rw [Finset.sum_sub_distrib, ← sG x]
    rw [this]
    exact loc_ofReal_le _ (fun i => by positivity) _ (loc_norm_sum_sq _)
  · unfold wint
    refine loc_lintegral_sum_lt (vol n z) _ (fun i x => ENNReal.ofReal
      (‖divF n z (g i) x - locD n z (χ i) G D x‖ ^ 2 * Real.exp (-(fun _ : M => (0 : ℝ)) x)))
      (fun i => loc_aem _ _ ((hdivc i).aestronglyMeasurable.sub (hP i).2.1.1)) (fun x => ?_) δ' δ
      (fun i => hg2 i) hδ'
    simp only [neg_zero, Real.exp_zero, mul_one]
    have : divF n z (fun x => ∑ i, g i x) x - D x =
        ∑ i, (divF n z (g i) x - locD n z (χ i) G D x) := by
      rw [hdiv x, Finset.sum_sub_distrib, ← sD x]
    rw [this]
    exact loc_ofReal_le _ (fun i => by positivity) _ (loc_norm_sum_sq _)
  · unfold n2
    refine loc_lintegral_sum_lt (vol n z) _ (fun i x => ENNReal.ofReal
      (sq2 n (sbar n z (g i) x - locS n z (χ i) G S x) * Real.exp (-(fun _ : M => (0 : ℝ)) x)))
      (fun i => aemeasurable_unweighted_two_form _ _ ((hsbc i).aestronglyMeasurable.sub (hP i).2.2.1.1)) (fun x => ?_) δ' δ
      (fun i => hg3 i) hδ'
    simp only [neg_zero, Real.exp_zero, mul_one]
    have : sbar n z (fun x => ∑ i, g i x) x - S x =
        fun j k => ∑ i, (sbar n z (g i) x - locS n z (χ i) G S x) j k := by
      funext j k
      simp only [Pi.sub_apply]
      rw [hsb x j k, sS x j k, Finset.sum_sub_distrib]
    rw [this]
    exact loc_ofReal_le _ (fun i => two_form_norm_sq_nonneg _ _) _ (two_form_sq_finset_sum_le _)
end ReciprocityTheory.L2DbarEstimates.F
