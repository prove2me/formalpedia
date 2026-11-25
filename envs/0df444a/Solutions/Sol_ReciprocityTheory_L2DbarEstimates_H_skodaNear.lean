-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.skodaNear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:37:52.43872+00:00
-- url     : https://prove2.me/submissions/9f559608-e94a-4558-8ef5-c303ad8380a1

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SmoothRLog
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_NearContinuousOfSmoothR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_near_vsq_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_near_continuous_vsq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_near_continuous_of_smoothR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_near_smooth_slice
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_l2w
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_perpTrace
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_skodaHyp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_skodaWeight
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_prodFin
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_lintegral_vol_prodFin


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
open scoped ENNReal InnerProductSpace
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] :
    SkodaNearStatement n M := by
  intro X p g φ₀ t hH hp hg hN hφ₀ hLφ₀ ht u u' hu' huu' F0 hF0
  have hz := X.isLocalHomeomorph
  have hgc : ∀ l, Continuous (g l) := fun l =>
    Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ (hg l))
  have huc : Continuous u' := Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ hu')
  have hNc := near_continuous_vsq g hgc
  have hNp : ∀ x, 0 < vsq (gv g x) := fun x => near_vsq_pos _ (hN x)
  have hW := skodaWeight n M X.z hz p g φ₀ t hg hN hφ₀ hLφ₀ ht.le
  have hWc : Continuous (skW g φ₀ t) := near_continuous_of_smoothR n X.z hz _ hW.1
  have hlogc : Continuous (fun x => Real.log (vsq (gv g x))) :=
    hNc.log fun x => (hNp x).ne'
  have hTr := fun x => perpTrace p (gv g x) (hN x)
  let F0f : M × Fin p → ℂ := fun q =>
    u' q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ)
  let c : M × Fin p → ℝ := fun q =>
    ‖u' q.1‖ ^ 2 * (1 - ‖g q.2 q.1‖ ^ 2 / vsq (gv g q.1)) / (t * vsq (gv g q.1))
  have hc0 : ∀ q, 0 ≤ c q := fun q =>
    div_nonneg (mul_nonneg (by positivity) ((hTr q.1).1 q.2)) (mul_pos ht (hNp q.1)).le
  have hcm : Measurable c := measurable_from_prod_countable_left fun i => by
    have : Continuous (fun x =>
        ‖u' x‖ ^ 2 * (1 - ‖g i x‖ ^ 2 / vsq (gv g x)) / (t * vsq (gv g x))) :=
      ((huc.norm.pow 2).mul (continuous_const.sub
        (((hgc i).norm.pow 2).div hNc fun x => (hNp x).ne'))).div
        (continuous_const.mul hNc) fun x => (mul_pos ht (hNp x)).ne'
    exact this.measurable
  have hsl : ∀ i, Smooth n X.z (fun x => F0f (x, i)) := fun i =>
    near_smooth_slice n X.z hz g hg hN u' hu' i
  have hF0fm : Measurable F0f := measurable_from_prod_countable_left fun i =>
    (Smooth.continuous n X.z hz _ (hsl i)).measurable
  have hF0fs : Smooth n (fun q : M × Fin p => X.z q.1) F0f :=
    (smooth_prodFin_iff n X.z hz p F0f).2 hsl
  have hph' : SmoothR n (fun q : M × Fin p => X.z q.1) (fun q => skW g φ₀ t q.1) :=
    (smooth_prodFin_iff n X.z hz p _).2 fun _ => hW.1
  have hLph' : LeviNonneg n (fun q : M × Fin p => X.z q.1) (fun q => skW g φ₀ t q.1) := by
    rintro ⟨x, i⟩ ξ
    rw [levi_prodFin n X.z hz p]
    exact hW.2.1 x ξ
  have hfm : Measurable (fun q => ENNReal.ofReal (c q)) := ENNReal.measurable_ofReal.comp hcm
  have hpt : ∀ (q : M × Fin p) (ξ : Fin n → ℂ),
      ENNReal.ofReal (‖dbarDot n (fun q : M × Fin p => X.z q.1) F0f q ξ‖ ^ 2) ≤
        ENNReal.ofReal (c q) *
          ENNReal.ofReal (Levi n (fun q : M × Fin p => X.z q.1) (fun q => skW g φ₀ t q.1) q ξ).re := by
    rintro ⟨x, i⟩ ξ
    have hd : dbarDot n (fun q : M × Fin p => X.z q.1) F0f (x, i) ξ =
        dbarDot n X.z (fun y => F0f (y, i)) x ξ := by
      simp only [dbarDot, db_prodFin n X.z hz p]
    rw [hd, levi_prodFin n X.z hz p, ← ENNReal.ofReal_mul (hc0 _)]
    exact ENNReal.ofReal_le_ofReal (skodaHyp n M X.z hz p g φ₀ t u' hg hu' hN hφ₀ hLφ₀ ht x i ξ)
  obtain ⟨F, hFh, hFb⟩ := hH (EtaleStein.prodFin n X p) (fun q => skW g φ₀ t q.1) F0f
    (fun q => ENNReal.ofReal (c q)) hph' hLph' hF0fs hfm hpt
  have hph'm : Measurable (fun q : M × Fin p => skW g φ₀ t q.1) :=
    hWc.measurable.comp measurable_fst
  have hψm : Measurable (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) :=
    (hWc.add hlogc).measurable
  have hpt0 : 0 ≤ ((p : ℝ) - 1) / t :=
    div_nonneg (sub_nonneg.2 (by exact_mod_cast hp)) ht.le
  have hEm : Measurable (fun q : M × Fin p =>
      ENNReal.ofReal (c q) * ENNReal.ofReal (Real.exp (-skW g φ₀ t q.1))) :=
    hfm.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hph'm.neg))
  have hR : ∫⁻ q, ENNReal.ofReal (c q) * ENNReal.ofReal (Real.exp (-skW g φ₀ t q.1))
      ∂vol n (fun q : M × Fin p => X.z q.1) =
      ENNReal.ofReal (((p : ℝ) - 1) / t) *
        wint n X.z u' (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) := by
    have hmi : ∀ i ∈ (Finset.univ : Finset (Fin p)), Measurable (fun x : M =>
        ENNReal.ofReal (c (x, i)) * ENNReal.ofReal (Real.exp (-skW g φ₀ t (x, i).1))) :=
      fun i _ => hEm.comp measurable_prodMk_right
    rw [lintegral_vol_prodFin n X.z hz p _ hEm, ← lintegral_finsetSum _ hmi]
    unfold wint
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    have hs : ∑ i, (1 - ‖g i x‖ ^ 2 / vsq (gv g x)) = (p : ℝ) - 1 := (hTr x).2
    calc ∑ i, ENNReal.ofReal (c (x, i)) * ENNReal.ofReal (Real.exp (-skW g φ₀ t (x, i).1))
        = ∑ i, ENNReal.ofReal (c (x, i) * Real.exp (-skW g φ₀ t x)) :=
          Finset.sum_congr rfl fun i _ => (ENNReal.ofReal_mul (hc0 _)).symm
      _ = ENNReal.ofReal (∑ i, c (x, i) * Real.exp (-skW g φ₀ t x)) :=
          (ENNReal.ofReal_sum_of_nonneg fun i _ =>
            mul_nonneg (hc0 _) (Real.exp_pos _).le).symm
      _ = ENNReal.ofReal (((p : ℝ) - 1) / t *
            (‖u' x‖ ^ 2 * Real.exp (-(skW g φ₀ t x + Real.log (vsq (gv g x)))))) := by
          congr 1
          have hsum : ∑ i, c (x, i) * Real.exp (-skW g φ₀ t x) =
              (‖u' x‖ ^ 2 / (t * vsq (gv g x)) * Real.exp (-skW g φ₀ t x)) *
                ∑ i, (1 - ‖g i x‖ ^ 2 / vsq (gv g x)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [c]
            ring
          have hNx := hNp x
          rw [hsum, hs, neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hNx]
          field_simp
      _ = _ := ENNReal.ofReal_mul hpt0
  have hl2 := l2w n M X.z _ hψm
  have hl2' := l2w n (M × Fin p) (fun q : M × Fin p => X.z q.1) _ hph'm
  obtain ⟨hu_fin, hu_norm⟩ := hl2.2.1 u
  have hwu : wint n X.z u' (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) =
      wint n X.z (u : M → ℂ) (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) :=
    lintegral_congr_ae (huu'.mono fun x hx => by dsimp only; rw [hx])
  have hR_fin : ENNReal.ofReal (((p : ℝ) - 1) / t) *
      wint n X.z u' (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hwu ▸ hu_fin)
  have hFb' : wint n (fun q : M × Fin p => X.z q.1) (fun q => F0f q - F q)
      (fun q => skW g φ₀ t q.1) ≤ ENNReal.ofReal (((p : ℝ) - 1) / t) *
        wint n X.z u' (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) := hR ▸ hFb
  have hwF0 : wint n (fun q : M × Fin p => X.z q.1) F0f (fun q => skW g φ₀ t q.1) < ⊤ := by
    have h1 := (hl2'.2.1 F0).1
    have h2 : wint n (fun q : M × Fin p => X.z q.1) (F0 : M × Fin p → ℂ)
        (fun q => skW g φ₀ t q.1) = wint n (fun q : M × Fin p => X.z q.1) F0f
        (fun q => skW g φ₀ t q.1) := lintegral_congr_ae (hF0.mono fun q hq => by dsimp only at hq ⊢; rw [hq])
    exact h2 ▸ h1
  have hFc : Continuous F :=
    Smooth.continuous n _ (EtaleStein.prodFin n X p).isLocalHomeomorph _ (Holo.smooth n _ _ hFh)
  have hwF : wint n (fun q : M × Fin p => X.z q.1) F (fun q => skW g φ₀ t q.1) < ⊤ := by
    have hle : wint n (fun q : M × Fin p => X.z q.1) F (fun q => skW g φ₀ t q.1) ≤
        2 * wint n (fun q : M × Fin p => X.z q.1) F0f (fun q => skW g φ₀ t q.1) +
          2 * wint n (fun q : M × Fin p => X.z q.1) (fun q => F0f q - F q)
            (fun q => skW g φ₀ t q.1) := by
      unfold wint
      rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
        ← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top, ← lintegral_add_left]
      · refine lintegral_mono fun q => ?_
        have hE := Real.exp_pos (-skW g φ₀ t q.1)
        have h3 : ‖F q‖ ≤ ‖F0f q‖ + ‖F0f q - F q‖ := by
          simpa using norm_sub_le (F0f q) (F0f q - F q)
        have h4 : ‖F q‖ ^ 2 ≤ 2 * ‖F0f q‖ ^ 2 + 2 * ‖F0f q - F q‖ ^ 2 := by
          nlinarith [sq_nonneg (‖F0f q‖ - ‖F0f q - F q‖), norm_nonneg (F q),
            norm_nonneg (F0f q), norm_nonneg (F0f q - F q)]
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [mul_le_mul_of_nonneg_right h4 hE.le]
      · exact measurable_const.mul (ENNReal.measurable_ofReal.comp
          (((hF0fm.norm.pow_const 2).mul (Real.measurable_exp.comp hph'm.neg))))
    exact hle.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofNat_lt_top hwF0,
      ENNReal.mul_lt_top ENNReal.ofNat_lt_top (hFb'.trans_lt hR_fin)⟩)
  obtain ⟨Fc, hFcF⟩ := hl2'.2.2 F hFc.aestronglyMeasurable hwF
  refine ⟨Fc, ⟨F, hFh, (hl2'.1 (fun q => (Fc : M × Fin p → ℂ) q = F q)).2 hFcF⟩, ?_⟩
  rw [(hl2'.2.1 (F0 - Fc)).2]
  have hsub : wint n (fun q : M × Fin p => X.z q.1) ((F0 - Fc : WeightedL2 n _ _) : M × Fin p → ℂ)
      (fun q => skW g φ₀ t q.1) =
      wint n (fun q : M × Fin p => X.z q.1) (fun q => F0f q - F q) (fun q => skW g φ₀ t q.1) := by
    refine lintegral_congr_ae ?_
    have h1 := (hl2'.1 (fun q => ((F0 - Fc : WeightedL2 n _ _) : M × Fin p → ℂ) q =
      ((F0 : M × Fin p → ℂ) - (Fc : M × Fin p → ℂ)) q)).1 (Lp.coeFn_sub F0 Fc)
    filter_upwards [h1, hF0, hFcF] with q h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  rw [hsub]
  calc _ ≤ (ENNReal.ofReal (((p : ℝ) - 1) / t) *
        wint n X.z u' (fun x => skW g φ₀ t x + Real.log (vsq (gv g x)))).toReal :=
        ENNReal.toReal_mono hR_fin.ne hFb'
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpt0, hwu, hu_norm]
end ReciprocityTheory.L2DbarEstimates.H
