-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.skoda
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:40:41.728959+00:00
-- url     : https://prove2.me/submissions/e5169d4e-8663-4c42-9e4b-5dfb781259c8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_NeedBergmanClosed
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaOps
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_NearContinuousOfSmoothR
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_OntoWithBoundTop
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_VolProdFinApply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_ae_fst_prodFin
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_ae_slice_prodFin
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_holo_finsum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_SkodaOperators_ae_slice_prodFin
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_l2w
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_skodaNear
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_skodaOps
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_skodaWeight
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_volOpenPos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_holo_prodFin_iff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_lintegral_vol_prodFin
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_ontoWithBound


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
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    (hH : ∀ p : ℕ, HStatement n (M × Fin p))
    (hB : ∀ p : ℕ, NeedBergmanClosed n (M × Fin p)) :
    SStatement n M := by
  intro X p g ph0 t f hp hg hnz hs hl ht hf hA
  have hz := X.isLocalHomeomorph
  have hz' : IsLocalHomeomorph (fun q : M × Fin p => X.z q.1) :=
    isLocalHomeomorph_comp_fst n X.z hz p
  have hp1 : 1 ≤ p := by omega
  have hp1r : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  have ht0 : 0 < t := by linarith
  have hgv : ∀ x, gv g x ≠ 0 := fun x h => by
    obtain ⟨i, hi⟩ := hnz x; exact hi (congrFun h i)
  have hN : ∀ x, 0 < vsq (gv g x) := fun x => by
    obtain ⟨i, hi⟩ := hnz x
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩
  have hgc : ∀ i, Continuous (g i) := fun i => Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ (hg i))
  have hfc : Continuous f := Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ hf)
  have hNc : Continuous fun x => vsq (gv g x) :=
    continuous_finsetSum _ fun i _ => ((hgc i).norm.pow 2)
  have hW := skodaWeight n M X.z hz p g ph0 t hg hgv hs hl ht0.le
  have hφc : Continuous (skW g ph0 t) :=
    (Complex.continuous_re.comp (Smooth.continuous n X.z hz _ hW.1)).congr fun x => Complex.ofReal_re _
  have hψ₂c : Continuous fun x => skW g ph0 t x + Real.log (vsq (gv g x)) :=
    hφc.add (hNc.log fun x => (hN x).ne')
  have hψ₁c : Continuous fun x : M × Fin p => skW g ph0 t x.1 := hφc.comp continuous_fst
  have hl2 := l2w n M X.z _ hψ₂c.measurable
  have hl1 := l2w n (M × Fin p) (fun q => X.z q.1) _ hψ₁c.measurable
  obtain ⟨G, Gs, hG, hGs, hadj, hiso⟩ := skodaOps n M X p g (skW g ph0 t) hg hgv hφc
  have hKc := hB p (fun q => X.z q.1) hz' _ hψ₁c
  have : CompleteSpace (holSub n (fun q : M × Fin p => X.z q.1) (fun x => skW g ph0 t x.1)) :=
    hKc.completeSpace_coe
  set K := holSub n (fun q : M × Fin p => X.z q.1) (fun x => skW g ph0 t x.1) with hKdef
  set Q := holSub n X.z (fun x => skW g ph0 t x + Real.log (vsq (gv g x))) with hQdef
  set c : ℝ := (t - ((p : ℝ) - 1)) / t with hcdef
  have hc : 0 < c := div_pos (by linarith) ht0
  have hc' : ∀ r : ℝ, c * r = r - ((p : ℝ) - 1) / t * r := fun r => by
    rw [hcdef]; field_simp

  have hnear : ∀ u ∈ Q, c * ‖u‖ ^ 2 ≤ ‖K.orthogonalProjectionOnto (Gs u)‖ ^ 2 := by
    intro u hu
    obtain ⟨u', hu', huu'⟩ := hu
    have huv : (u : M → ℂ) =ᵐ[vol n X.z] u' := (hl2.1 _).1 huu'
    have hF0 : (Gs u : M × Fin p → ℂ) =ᵐ[vol n (fun q : M × Fin p => X.z q.1)]
        fun x => u' x.1 * (starRingEnd ℂ) (g x.2 x.1) / ((vsq (gv g x.1) : ℝ) : ℂ) := by
      filter_upwards [hGs u, ae_fst_prodFin n X.z hz p huv] with q h1 h2
      rw [h1, h2]
    obtain ⟨F, hFK, hFd⟩ :=
      skodaNear n M X p g ph0 t (hH p) hp1 hg hgv hs hl ht0 u u' hu' huv (Gs u) hF0
    have hya : Gs u - K.starProjection (Gs u) ∈ Kᗮ := K.sub_starProjection_mem_orthogonal (Gs u)
    have hperp : ⟪K.starProjection (Gs u), Gs u - K.starProjection (Gs u)⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (K.orthogonalProjectionOnto (Gs u)).2 hya
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hperp
    rw [add_sub_cancel, hiso u] at hpy
    have hmin : ‖Gs u - K.starProjection (Gs u)‖ ≤ ‖Gs u - F‖ := by
      rw [Submodule.starProjection_minimal (U := K) (Gs u)]
      exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨F, hFK⟩ : K)
    have hmin2 := pow_le_pow_left₀ (norm_nonneg _) hmin 2
    have hnorm : ‖K.orthogonalProjectionOnto (Gs u)‖ = ‖K.starProjection (Gs u)‖ := rfl
    rw [hnorm, hc']
    nlinarith [hpy, hmin2, hFd]

  have hAeq : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 * (∑ i, ‖g i x‖ ^ 2) ^ (-(t + 1)) *
      Real.exp (-ph0 x)) ∂vol n X.z =
      wint n X.z f (fun x => skW g ph0 t x + Real.log (vsq (gv g x))) := by
    unfold wint
    refine lintegral_congr fun x => ?_
    rw [show (∑ i, ‖g i x‖ ^ 2) = vsq (gv g x) from rfl, Real.rpow_def_of_pos (hN x), mul_assoc,
      ← Real.exp_add]
    congr 3
    simp only [skW]; ring
  obtain ⟨fL, hfL⟩ := hl2.2.2 f hfc.aestronglyMeasurable (hAeq ▸ hA)
  have hfLQ : fL ∈ Q := ⟨f, hf, (hl2.1 _).2 hfL⟩
  obtain ⟨⟨hv, hvK⟩, hhG, -, hhn⟩ := ontoWithBound ℂ K _ ((G : _ →ₗ[ℂ] _).comp K.subtype)
    ((K.orthogonalProjectionOnto.comp Gs : _ →L[ℂ] K) : _ →ₗ[ℂ] K) 0 Q c hc
    (fun u _ x => by simp [hadj]) (fun u hu e => by simpa using hnear u hu) fL hfLQ
  have hhn' : c * ‖hv‖ ^ 2 ≤ ‖fL‖ ^ 2 := hhn
  obtain ⟨hh', hhol', hae'⟩ := hvK
  have hae'v : (hv : M × Fin p → ℂ) =ᵐ[vol n (fun q : M × Fin p => X.z q.1)] hh' :=
    (hl1.1 _).1 hae'
  have hslice : ∀ᵐ x ∂vol n X.z, ∀ i, (hv : M × Fin p → ℂ) (x, i) = hh' (x, i) :=
    ae_all_iff.2 fun i => ae_slice_prodFin n X.z hz p hae'v i
  have hhol : ∀ i, Holo n X.z (fun x => hh' (x, i)) := (holo_prodFin_iff n X.z hz p hh').1 hhol'
  have hSh : Holo n X.z (fun x => ∑ i, g i x * hh' (x, i)) :=
    holo_finsum n X.z _ fun i => Holo.mul n X.z _ _ (hg i) (hhol i)
  have hGS : (G hv : M → ℂ) =ᵐ[vol n X.z] fun x => ∑ i, g i x * hh' (x, i) := by
    filter_upwards [hG hv, hslice] with x h1 h2
    rw [h1]; exact Finset.sum_congr rfl fun i _ => by rw [h2 i]
  have hGQ : G hv ∈ Q := ⟨_, hSh, (hl2.1 _).2 hGS⟩
  have hGf : G hv = fL := by
    have h1 := hhG (G hv - fL) (Q.sub_mem hGQ hfLQ)
    simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
      Submodule.coe_subtype] at h1
    rw [← sub_eq_zero, ← inner_sub_right] at h1
    exact sub_eq_zero.1 (inner_self_eq_zero.1 h1)
  have hfS : ∀ x, f x = ∑ i, g i x * hh' (x, i) := by
    have hae : ∀ᵐ x ∂vol n X.z, f x = ∑ i, g i x * hh' (x, i) := by
      filter_upwards [hGS, hfL] with x h1 h2
      rw [← h2, ← hGf, h1]
    have hSc : Continuous fun x => ∑ i, g i x * hh' (x, i) :=
      Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ hSh)
    by_contra hne
    obtain ⟨x0, hx0⟩ := not_forall.1 hne
    have hpos := volOpenPos n M X.z hz _ (isOpen_ne_fun hfc hSc) ⟨x0, hx0⟩
    rw [ae_iff] at hae
    exact hpos.ne' hae
  have hh'c : Continuous hh' := Smooth.continuous n _ hz' _ (Holo.smooth n _ _ hhol')
  have hmeas : ∀ i, Measurable fun x =>
      ENNReal.ofReal (‖hh' (x, i)‖ ^ 2 * Real.exp (-skW g ph0 t x)) := fun i =>
    (ENNReal.continuous_ofReal.comp (((hh'c.comp (continuous_id.prodMk continuous_const)).norm.pow 2).mul
      (Real.continuous_exp.comp hφc.neg))).measurable
  refine ⟨fun i x => hh' (x, i), hhol, hfS, ?_⟩
  beta_reduce
  calc ∫⁻ x, ENNReal.ofReal ((∑ i, ‖hh' (x, i)‖ ^ 2) * (∑ i, ‖g i x‖ ^ 2) ^ (-t) *
          Real.exp (-ph0 x)) ∂vol n X.z
        = ∑ i, ∫⁻ x, ENNReal.ofReal (‖hh' (x, i)‖ ^ 2 * Real.exp (-skW g ph0 t x)) ∂vol n X.z := by
        rw [← lintegral_finsetSum _ (fun i _ => hmeas i)]
        refine lintegral_congr fun x => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
        congr 1
        rw [show (∑ i, ‖g i x‖ ^ 2) = vsq (gv g x) from rfl, Real.rpow_def_of_pos (hN x),
          Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        simp only [skW]; ring
    _ = wint n (fun q : M × Fin p => X.z q.1) hh' (fun x => skW g ph0 t x.1) := by
        unfold wint
        have hm : Measurable fun q : M × Fin p =>
            ENNReal.ofReal (‖hh' q‖ ^ 2 * Real.exp (-skW g ph0 t q.1)) :=
          (ENNReal.continuous_ofReal.comp
            ((hh'c.norm.pow 2).mul (Real.continuous_exp.comp hψ₁c.neg))).measurable
        rw [lintegral_vol_prodFin n X.z hz p _ hm]
    _ = wint n (fun q : M × Fin p => X.z q.1) hv (fun x => skW g ph0 t x.1) := by
        unfold wint
        exact lintegral_congr_ae (by filter_upwards [hae'v] with q hq; rw [hq])
    _ = ENNReal.ofReal (‖hv‖ ^ 2) := by
        rw [(hl1.2.1 hv).2, ENNReal.ofReal_toReal (hl1.2.1 hv).1.ne]
    _ ≤ ENNReal.ofReal (t / (t - ((p : ℝ) - 1)) * ‖fL‖ ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have hci : t / (t - ((p : ℝ) - 1)) = c⁻¹ := by rw [hcdef, inv_div]
        rw [hci, ← div_eq_inv_mul, le_div_iff₀ hc]
        linarith [hhn']
    _ = ENNReal.ofReal (t / (t - ((p : ℝ) - 1))) *
          wint n X.z f (fun x => skW g ph0 t x + Real.log (vsq (gv g x))) := by
        rw [ENNReal.ofReal_mul (div_nonneg ht0.le (by linarith)), (hl2.2.1 fL).2,
          ENNReal.ofReal_toReal (hl2.2.1 fL).1.ne]
        congr 1
        unfold wint
        exact lintegral_congr_ae (by filter_upwards [hfL] with x hx; rw [hx])
    _ = _ := by rw [hAeq]
end ReciprocityTheory.L2DbarEstimates.H
