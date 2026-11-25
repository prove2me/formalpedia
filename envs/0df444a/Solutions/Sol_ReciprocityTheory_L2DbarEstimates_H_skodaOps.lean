-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.skodaOps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:49:15.842044+00:00
-- url     : https://prove2.me/submissions/5861532d-8720-4994-8765-c2558e3359eb

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_IntegrableSliceProdFin
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaOps
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_SkodaOperators_ae_lift_prodFin
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_SkodaOperators_ae_slice_prodFin
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_SkodaOperators_wint_G_le
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_SkodaOperators_wint_Gs_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_l2w
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
open scoped ENNReal InnerProductSpace
private theorem wint_congr_ae (n : ℕ) {N : Type*} [MeasurableSpace N] (z : N → V n)
    (ψ : N → ℝ) {f₁ f₂ : N → ℂ} (h : f₁ =ᵐ[vol n z] f₂) : wint n z f₁ ψ = wint n z f₂ ψ := by
  unfold wint
  refine lintegral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]
private theorem exists_pow_mul_eq_eval₂_theta (n : ℕ) {N : Type*} [MeasurableSpace N] (z : N → V n) (ψ : N → ℝ)
    (hψ : Measurable ψ) (F : WeightedL2 n z ψ) :
    ∃ f : N → ℂ, Measurable f ∧ (F : N → ℂ) =ᵐ[vol n z] f := by
  obtain ⟨A1, -, -⟩ := l2w n N z ψ hψ
  refine ⟨(Lp.aestronglyMeasurable F).mk _,
    (Lp.aestronglyMeasurable F).stronglyMeasurable_mk.measurable, ?_⟩
  exact (A1 (fun x => (F : N → ℂ) x = (Lp.aestronglyMeasurable F).mk _ x)).mp
    (Lp.aestronglyMeasurable F).ae_eq_mk
private theorem exists_clm_weightedL2_of_bounded (n : ℕ) {N₁ N₂ : Type*} [MeasurableSpace N₁] [MeasurableSpace N₂]
    (z₁ : N₁ → V n) (z₂ : N₂ → V n) (ψ₁ : N₁ → ℝ) (ψ₂ : N₂ → ℝ)
    (hψ₁ : Measurable ψ₁) (hψ₂ : Measurable ψ₂) (T : (N₁ → ℂ) → (N₂ → ℂ))
    (hT : ∀ (a : ℂ) (f₁ f₂ : N₁ → ℂ), T (fun x => a * f₁ x + f₂ x) = fun y => a * T f₁ y + T f₂ y)
    (hTae : ∀ f₁ f₂ : N₁ → ℂ, f₁ =ᵐ[vol n z₁] f₂ → T f₁ =ᵐ[vol n z₂] T f₂)
    (hex : ∀ F : WeightedL2 n z₁ ψ₁, ∃ H : WeightedL2 n z₂ ψ₂, (H : N₂ → ℂ) =ᵐ[vol n z₂] T F)
    (hb : ∀ (F : WeightedL2 n z₁ ψ₁) (H : WeightedL2 n z₂ ψ₂), (H : N₂ → ℂ) =ᵐ[vol n z₂] T F → ‖H‖ ≤ ‖F‖) :
    ∃ L : WeightedL2 n z₁ ψ₁ →L[ℂ] WeightedL2 n z₂ ψ₂, ∀ F, (L F : N₂ → ℂ) =ᵐ[vol n z₂] T F := by
  obtain ⟨A1, -, -⟩ := l2w n N₁ z₁ ψ₁ hψ₁
  obtain ⟨B1, -, -⟩ := l2w n N₂ z₂ ψ₂ hψ₂
  choose L hL using hex
  have key : ∀ (a : ℂ) (F₁ F₂ : WeightedL2 n z₁ ψ₁), L (a • F₁ + F₂) = a • L F₁ + L F₂ := by
    intro a F₁ F₂
    apply Lp.ext
    have h2 : ((a • F₁ + F₂ : WeightedL2 n z₁ ψ₁) : N₁ → ℂ) =ᵐ[vol n z₁] fun x => a * F₁ x + F₂ x :=
      (A1 (fun x => ((a • F₁ + F₂ : WeightedL2 n z₁ ψ₁) : N₁ → ℂ) x = a * F₁ x + F₂ x)).mp (by
        filter_upwards [Lp.coeFn_add (a • F₁) F₂, Lp.coeFn_smul a F₁] with x hx1 hx2
        rw [hx1, Pi.add_apply, hx2, Pi.smul_apply, smul_eq_mul])
    have h3 : ((a • L F₁ + L F₂ : WeightedL2 n z₂ ψ₂) : N₂ → ℂ) =ᵐ[vol n z₂]
        fun y => a * L F₁ y + L F₂ y :=
      (B1 (fun y => ((a • L F₁ + L F₂ : WeightedL2 n z₂ ψ₂) : N₂ → ℂ) y = a * L F₁ y + L F₂ y)).mp (by
        filter_upwards [Lp.coeFn_add (a • L F₁) (L F₂), Lp.coeFn_smul a (L F₁)] with y hy1 hy2
        rw [hy1, Pi.add_apply, hy2, Pi.smul_apply, smul_eq_mul])
    refine (B1 (fun y => ((L (a • F₁ + F₂) : WeightedL2 n z₂ ψ₂) : N₂ → ℂ) y =
      ((a • L F₁ + L F₂ : WeightedL2 n z₂ ψ₂) : N₂ → ℂ) y)).mpr ?_
    filter_upwards [hL (a • F₁ + F₂), hTae _ _ h2, h3, hL F₁, hL F₂] with y e1 e2 e3 e4 e5
    rw [e1, e2, hT a (F₁ : N₁ → ℂ) (F₂ : N₁ → ℂ), e3, e4, e5]
  have L0 : L 0 = 0 := by
    have h := key 1 0 0
    simp only [one_smul, add_zero] at h
    have h' : L 0 + 0 = L 0 + L 0 := by rw [add_zero]; exact h
    exact (add_left_cancel h').symm
  refine ⟨LinearMap.mkContinuous
    { toFun := L
      map_add' := fun F₁ F₂ => by simpa using key 1 F₁ F₂
      map_smul' := fun c F => by simpa [L0] using key c F 0 } 1
    (fun F => by simpa using hb F (L F) (hL F)), fun F => hL F⟩
private theorem inner_isometry_eq_inner_left_inverse {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (S : F →L[ℂ] E) (G : E →L[ℂ] F) (hS : ∀ w, ‖S w‖ = ‖w‖) (hG : ∀ h, ‖G h‖ ≤ ‖h‖)
    (hGS : ∀ w, G (S w) = w) (w : F) (h : E) : ⟪S w, h⟫_ℂ = ⟪w, G h⟫_ℂ := by
  set A := ContinuousLinearMap.adjoint S with hA
  let Si : F →ₗᵢ[ℂ] E := { toLinearMap := S.toLinearMap, norm_map' := hS }
  have hSS : ∀ x y, ⟪S x, S y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y => Si.inner_map_map x y
  have hAS : ∀ x, A (S x) = x := by
    intro x
    apply ext_inner_left ℂ
    intro v
    rw [hA, ContinuousLinearMap.adjoint_inner_right, hSS]
  set k := h - S (A h) with hk0
  have hk : ∀ y, ⟪S y, k⟫_ℂ = 0 := by
    intro y
    rw [← ContinuousLinearMap.adjoint_inner_right, ← hA, hk0, map_sub, hAS, sub_self,
      inner_zero_right]
  have hGk : G k = 0 := by
    by_contra hne
    have ha : 0 < ‖G k‖ := norm_pos_iff.mpr hne
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ‖k‖ ^ 2 / ‖G k‖ ^ 2 := ⟨_, rfl⟩
    have hs0 : 0 ≤ s := by rw [hs]; positivity
    have hsa : s * ‖G k‖ ^ 2 = ‖k‖ ^ 2 := by
      rw [hs]; exact div_mul_cancel₀ _ (pow_pos ha 2).ne'
    have h1 : ‖G (S ((s : ℂ) • G k) + k)‖ ≤ ‖S ((s : ℂ) • G k) + k‖ := hG _
    rw [map_add, hGS] at h1
    have h2 : ‖(s : ℂ) • G k + G k‖ = (s + 1) * ‖G k‖ := by
      have e : (s : ℂ) • G k + G k = ((s + 1 : ℝ) : ℂ) • G k := by
        rw [Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul]
      rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have h3 : ‖S ((s : ℂ) • G k) + k‖ * ‖S ((s : ℂ) • G k) + k‖ =
        (s * ‖G k‖) * (s * ‖G k‖) + ‖k‖ * ‖k‖ := by
      rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (hk _), hS, norm_smul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    rw [h2] at h1
    have h4 := mul_self_le_mul_self (by positivity) h1
    nlinarith [h3, h4, hsa, mul_pos ha ha, mul_nonneg hs0 (mul_self_nonneg ‖G k‖)]
  have hdec : h = S (A h) + k := by rw [hk0]; abel
  have hGh : G h = A h := by
    calc G h = G (S (A h) + k) := by rw [← hdec]
      _ = A h := by rw [map_add, hGS, hGk, add_zero]
  rw [hGh, hA, ContinuousLinearMap.adjoint_inner_right]
end ReciprocityTheory.L2DbarEstimates.H
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
open scoped ENNReal InnerProductSpace
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] :
    SkodaOpsStatement n M := by
  intro X p g φ hg hgv hφ
  have hz : IsLocalHomeomorph X.z := X.isLocalHomeomorph
  have hgc : ∀ l, Continuous (g l) := fun l =>
    Smooth.continuous n X.z hz (g l) (Holo.smooth n X.z (g l) (hg l))
  have hgm : ∀ l, Measurable (g l) := fun l => (hgc l).measurable
  have hgq : Measurable fun q : M × Fin p => g q.2 q.1 :=
    measurable_from_prod_countable_left fun i => hgm i
  have hN : ∀ x, 0 < vsq (gv g x) := by
    intro x
    obtain ⟨i, hi⟩ : ∃ i, gv g x i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hgv x (funext hc)
    have h1 : 0 < ‖gv g x i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi) 2
    have h2 : ‖gv g x i‖ ^ 2 ≤ ∑ j, ‖gv g x j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖gv g x j‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    unfold vsq
    linarith
  have hvc : Continuous fun x => vsq (gv g x) := by
    show Continuous fun x => ∑ i, ‖g i x‖ ^ 2
    exact continuous_finset_sum _ fun i _ => ((hgc i).norm).pow 2
  have hvm : Measurable fun x => vsq (gv g x) := hvc.measurable
  have hφm : Measurable φ := hφ.measurable
  have hψm : Measurable fun x => φ x + Real.log (vsq (gv g x)) :=
    hφm.add (Real.measurable_log.comp hvm)
  have hψpm : Measurable fun x : M × Fin p => φ x.1 := hφm.comp measurable_fst
  obtain ⟨A1, A2, A3⟩ := l2w n M X.z (fun x => φ x + Real.log (vsq (gv g x))) hψm
  obtain ⟨B1, B2, B3⟩ := l2w n (M × Fin p) (fun q : M × Fin p => X.z q.1)
    (fun x : M × Fin p => φ x.1) hψpm
  have hcn : Measurable fun q : M × Fin p => ((vsq (gv g q.1) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (hvm.comp measurable_fst)
  have hcj : Measurable fun q : M × Fin p => (starRingEnd ℂ) (g q.2 q.1) :=
    Complex.continuous_conj.measurable.comp hgq
  have hlift : ∀ f₁ f₂ : M → ℂ, f₁ =ᵐ[vol n X.z] f₂ →
      ∀ᵐ q ∂vol n (fun q : M × Fin p => X.z q.1), f₁ q.1 = f₂ q.1 := fun f₁ f₂ h =>
    ae_lift_prodFin X.z hz p (P := fun x => f₁ x = f₂ x) h
  have hslice : ∀ h₁ h₂ : M × Fin p → ℂ, h₁ =ᵐ[vol n (fun q : M × Fin p => X.z q.1)] h₂ →
      ∀ᵐ x ∂vol n X.z, ∀ i, h₁ (x, i) = h₂ (x, i) := fun h₁ h₂ h =>
    ae_all_iff.mpr fun i => ae_slice_prodFin X.z hz p (P := fun q => h₁ q = h₂ q) h i
  have hcancel : ∀ (x : M) (c : ℂ),
      ∑ i, g i x * (c * (starRingEnd ℂ) (g i x) / ((vsq (gv g x) : ℝ) : ℂ)) = c := by
    intro x c
    have hV : ((vsq (gv g x) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hN x).ne'
    have hs : ∑ i, g i x * (starRingEnd ℂ) (g i x) = ((vsq (gv g x) : ℝ) : ℂ) := by
      rw [show vsq (gv g x) = ∑ i, ‖g i x‖ ^ 2 from rfl, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    calc ∑ i, g i x * (c * (starRingEnd ℂ) (g i x) / ((vsq (gv g x) : ℝ) : ℂ))
        = c * (∑ i, g i x * (starRingEnd ℂ) (g i x)) / ((vsq (gv g x) : ℝ) : ℂ) := by
          rw [Finset.mul_sum, Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = c := by rw [hs, mul_div_assoc, div_self hV, mul_one]
  have hGsn : ∀ (w : WeightedL2 n X.z (fun x => φ x + Real.log (vsq (gv g x))))
      (H : WeightedL2 n (fun q : M × Fin p => X.z q.1) (fun x : M × Fin p => φ x.1)),
      (H : M × Fin p → ℂ) =ᵐ[vol n (fun q : M × Fin p => X.z q.1)]
        (fun q => (w : M → ℂ) q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ)) →
      ‖H‖ = ‖w‖ := by
    intro w H hH
    obtain ⟨wm, hwm, hwae⟩ := exists_pow_mul_eq_eval₂_theta n X.z _ hψm w
    have hH' : (H : M × Fin p → ℂ) =ᵐ[vol n (fun q : M × Fin p => X.z q.1)]
        (fun q => wm q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ)) := by
      filter_upwards [hH, hlift _ _ hwae] with q h1 h2
      rw [h1, h2]
    have e : ‖H‖ ^ 2 = ‖w‖ ^ 2 := by
      rw [(B2 H).2, (A2 w).2, wint_congr_ae n _ (fun x : M × Fin p => φ x.1) hH',
        wint_Gs_eq X.z hz p g hgm φ hφm hN wm hwm,
        wint_congr_ae n X.z (fun x => φ x + Real.log (vsq (gv g x))) hwae]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp e
  have hGb : ∀ (h : WeightedL2 n (fun q : M × Fin p => X.z q.1) (fun x : M × Fin p => φ x.1))
      (H : WeightedL2 n X.z (fun x => φ x + Real.log (vsq (gv g x)))),
      (H : M → ℂ) =ᵐ[vol n X.z] (fun x => ∑ i, g i x * (h : M × Fin p → ℂ) (x, i)) →
      ‖H‖ ≤ ‖h‖ := by
    intro h H hH
    obtain ⟨hm, hhm, hhae⟩ := exists_pow_mul_eq_eval₂_theta n (fun q : M × Fin p => X.z q.1) _ hψpm h
    have hH' : (H : M → ℂ) =ᵐ[vol n X.z] (fun x => ∑ i, g i x * hm (x, i)) := by
      filter_upwards [hH, hslice _ _ hhae] with x h1 h2
      rw [h1]
      exact Finset.sum_congr rfl fun i _ => by rw [h2 i]
    have hfin : wint n (fun q : M × Fin p => X.z q.1) hm (fun x : M × Fin p => φ x.1) ≠ ⊤ := by
      rw [← wint_congr_ae n _ (fun x : M × Fin p => φ x.1) hhae]
      exact (B2 h).1.ne
    have e : ‖H‖ ^ 2 ≤ ‖h‖ ^ 2 := by
      rw [(A2 H).2, (B2 h).2,
        wint_congr_ae n X.z (fun x => φ x + Real.log (vsq (gv g x))) hH',
        wint_congr_ae n _ (fun x : M × Fin p => φ x.1) hhae]
      exact ENNReal.toReal_mono hfin (wint_G_le X.z hz p g φ hφm hN hm hhm)
    nlinarith [norm_nonneg H, norm_nonneg h]
  obtain ⟨Gs, hGs⟩ := exists_clm_weightedL2_of_bounded n X.z (fun q : M × Fin p => X.z q.1)
    (fun x => φ x + Real.log (vsq (gv g x))) (fun x : M × Fin p => φ x.1) hψm hψpm
    (fun f q => f q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ))
    (fun a f₁ f₂ => by funext q; beta_reduce; ring)
    (fun f₁ f₂ h => by
      filter_upwards [hlift f₁ f₂ h] with q hq
      beta_reduce
      rw [hq])
    (fun w => by
      obtain ⟨wm, hwm, hwae⟩ := exists_pow_mul_eq_eval₂_theta n X.z _ hψm w
      have hmeas : Measurable (fun q : M × Fin p =>
          wm q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ)) :=
        ((hwm.comp measurable_fst).mul hcj).div hcn
      obtain ⟨H, hH⟩ := B3 _ hmeas.aestronglyMeasurable (by
        rw [wint_Gs_eq X.z hz p g hgm φ hφm hN wm hwm,
          ← wint_congr_ae n X.z (fun x => φ x + Real.log (vsq (gv g x))) hwae]
        exact (A2 w).1)
      refine ⟨H, ?_⟩
      filter_upwards [hH, hlift _ _ hwae] with q h1 h2
      beta_reduce
      rw [h1, h2])
    (fun w H hH => le_of_eq (hGsn w H hH))
  obtain ⟨G, hG⟩ := exists_clm_weightedL2_of_bounded n (fun q : M × Fin p => X.z q.1) X.z (fun x : M × Fin p => φ x.1)
    (fun x => φ x + Real.log (vsq (gv g x))) hψpm hψm
    (fun h x => ∑ i, g i x * h (x, i))
    (fun a h₁ h₂ => by
      funext x
      beta_reduce
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun h₁ h₂ hh => by
      filter_upwards [hslice h₁ h₂ hh] with x hx
      beta_reduce
      exact Finset.sum_congr rfl fun i _ => by rw [hx i])
    (fun h => by
      obtain ⟨hm, hhm, hhae⟩ := exists_pow_mul_eq_eval₂_theta n (fun q : M × Fin p => X.z q.1) _ hψpm h
      have hmeas : Measurable (fun x : M => ∑ i, g i x * hm (x, i)) :=
        Finset.measurable_sum _ fun i _ => (hgm i).mul (hhm.comp (by fun_prop))
      obtain ⟨H, hH⟩ := A3 _ hmeas.aestronglyMeasurable
        (lt_of_le_of_lt (wint_G_le X.z hz p g φ hφm hN hm hhm) (by
          rw [← wint_congr_ae n _ (fun x : M × Fin p => φ x.1) hhae]
          exact (B2 h).1))
      refine ⟨H, ?_⟩
      filter_upwards [hH, hslice _ _ hhae] with x h1 h2
      beta_reduce
      rw [h1]
      exact Finset.sum_congr rfl fun i _ => by rw [h2 i])
    (fun h H hH => hGb h H hH)
  have hGsiso : ∀ w, ‖Gs w‖ = ‖w‖ := fun w => hGsn w (Gs w) (hGs w)
  have hGS : ∀ w, G (Gs w) = w := by
    intro w
    apply Lp.ext
    refine (A1 (fun x => (G (Gs w) : M → ℂ) x = (w : M → ℂ) x)).mpr ?_
    filter_upwards [hG (Gs w), hslice _ _ (hGs w)] with x h1 h2
    rw [h1]
    calc ∑ i, g i x * (Gs w : M × Fin p → ℂ) (x, i)
        = ∑ i, g i x * ((w : M → ℂ) x * (starRingEnd ℂ) (g i x) / ((vsq (gv g x) : ℝ) : ℂ)) :=
          Finset.sum_congr rfl fun i _ => by rw [h2 i]
      _ = (w : M → ℂ) x := hcancel x _
  exact ⟨G, Gs, hG, hGs, fun w h => inner_isometry_eq_inner_left_inverse Gs G hGsiso (fun h => hGb h (G h) (hG h)) hGS w h,
    hGsiso⟩
end ReciprocityTheory.L2DbarEstimates.H
