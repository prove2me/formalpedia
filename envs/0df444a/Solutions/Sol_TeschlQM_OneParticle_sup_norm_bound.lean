-- Prove2me | solution 1 for TeschlQM.OneParticle.sup_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-07T14:46:36.640017+00:00
-- url     : https://prove2.me/submissions/98494bd6-f059-4930-8cb1-ab06635d2983

import Mathlib
import Definitions.Def_TeschlQM_OneParticle_freeHamiltonian

open MeasureTheory FourierTransform SchwartzMap
open scoped ContDiff ZeroAtInfty InnerProductSpace
open Filter Topology
open TeschlQM.OneParticle

namespace SobAux

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

lemma fourierInv_fun_eq (G : V → ℂ) :
    𝓕⁻ G = VectorFourier.fourierIntegral Real.fourierChar volume (-innerₗ V) G := rfl

lemma continuous_fourierInv_fun {G : V → ℂ} (hG : Integrable G) : Continuous (𝓕⁻ G) := by
  rw [fourierInv_fun_eq]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simp; exact continuous_inner.neg) hG

lemma integral_fourierInv_smul_eq_fun {f g : V → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕⁻ f ξ • g ξ = ∫ x, f x • 𝓕⁻ g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar)
    (μ := volume) (ν := volume) (L := -innerₗ V) Real.continuous_fourierChar
    (by simp; exact continuous_inner.neg) hf hg
  have hflip : (-innerₗ V).flip = -innerₗ V := by
    ext x y
    simp [real_inner_comm]
  rw [hflip] at h
  exact h

lemma fourierInv_L2_ae_eq (g : Lp ℂ 2 (volume : Measure V)) (hg : Integrable (g : V → ℂ)) :
    ((𝓕⁻ g : Lp ℂ 2 (volume : Measure V)) : V → ℂ) =ᵐ[volume] 𝓕⁻ (g : V → ℂ) := by
  have hc := continuous_fourierInv_fun hg
  have hA : LocallyIntegrable (((𝓕⁻ g : Lp ℂ 2 (volume : Measure V)) : V → ℂ)) volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hli : LocallyIntegrable (fun x => ((𝓕⁻ g : Lp ℂ 2 (volume : Measure V)) : V → ℂ) x -
      𝓕⁻ (g : V → ℂ) x) volume := hA.sub hc.locallyIntegrable
  have key := ae_eq_zero_of_integral_contDiff_smul_eq_zero hli ?_
  · filter_upwards [key] with x hx using sub_eq_zero.mp hx
  intro φ hφs hφc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := Complex.ofRealCLM.contDiff.comp hφs
  set ψ := hg₁.toSchwartzMap hg₂ with hψdef
  have hψ : ∀ x, ψ x = (φ x : ℂ) := fun x => by simp [ψ]
  have e1 : ∫ x, φ x • ((𝓕⁻ g : Lp ℂ 2 (volume : Measure V)) : V → ℂ) x =
      ∫ ξ, (𝓕⁻ (ψ : V → ℂ)) ξ • g ξ := by
    have := Lp.toTemperedDistribution_apply (𝓕⁻ g) ψ
    rw [← Lp.fourierInv_toTemperedDistribution_eq, TemperedDistribution.fourierInv_apply,
      Lp.toTemperedDistribution_apply, SchwartzMap.fourierInv_coe] at this
    rw [this]
    simp [hψ, Complex.real_smul]
  have e2 : ∫ x, φ x • 𝓕⁻ (g : V → ℂ) x = ∫ ξ, (𝓕⁻ (ψ : V → ℂ)) ξ • g ξ := by
    rw [integral_fourierInv_smul_eq_fun ψ.integrable hg]
    simp [hψ, Complex.real_smul]
  have i1 : Integrable (fun x => φ x • ((𝓕⁻ g : Lp ℂ 2 (volume : Measure V)) : V → ℂ) x) :=
    hA.integrable_smul_left_of_hasCompactSupport hφs.continuous hφc
  have i2 : Integrable (fun x => φ x • 𝓕⁻ (g : V → ℂ) x) :=
    hc.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφs.continuous hφc
  simp_rw [smul_sub]
  rw [integral_sub i1 i2, e1, e2, sub_self]

lemma tendsto_fourierInv_fun (G : V → ℂ) : Tendsto (𝓕⁻ G) (cocompact V) (𝓝 0) := by
  rw [Real.fourierInv_eq_fourier_comp_neg]
  exact tendsto_integral_exp_inner_smul_cocompact (fun x => G (-x))

/-- The inverse Fourier integral of an integrable function, as a `C₀` function. -/
noncomputable def c0OfL1 (G : V → ℂ) (hG : Integrable G) : V →C₀ ℂ where
  toFun := 𝓕⁻ G
  continuous_toFun := continuous_fourierInv_fun hG
  zero_at_infty' := tendsto_fourierInv_fun G

@[simp] lemma coe_c0OfL1 (G : V → ℂ) (hG : Integrable G) : ⇑(c0OfL1 G hG) = 𝓕⁻ G := rfl

lemma norm_c0OfL1_le (G : V → ℂ) (hG : Integrable G) : ‖c0OfL1 G hG‖ ≤ ∫ v, ‖G v‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
    BoundedContinuousFunction.norm_le (integral_nonneg fun _ => norm_nonneg _)]
  intro x
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

variable {n : ℕ}

lemma re_inner_pt' (a b : ℂ) : (⟪a, b⟫_ℂ).re = a.re * b.re + a.im * b.im := by
  simp
  ring

/-- The weight `(2π|ξ|)² + t`. -/
noncomputable def wt (t : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) : ℝ := (2 * Real.pi * ‖ξ‖) ^ 2 + t

lemma wt_pos {t : ℝ} (ht : 0 < t) (ξ : EuclideanSpace ℝ (Fin n)) : 0 < wt t ξ := by
  unfold wt
  positivity

lemma continuous_wt (t : ℝ) : Continuous (fun ξ : EuclideanSpace ℝ (Fin n) => wt t ξ) := by
  unfold wt
  fun_prop

lemma wt_bound {t : ℝ} (ht : 1 ≤ t) (ξ : EuclideanSpace ℝ (Fin n)) :
    (wt t ξ)⁻¹ ^ 2 ≤ 4 * (1 + ‖ξ‖) ^ (-4 : ℝ) := by
  have hr := norm_nonneg ξ
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h1 : ‖ξ‖ ^ 2 ≤ (2 * Real.pi * ‖ξ‖) ^ 2 :=
    pow_le_pow_left₀ hr (le_mul_of_one_le_left hr hpi) 2
  have hw : ‖ξ‖ ^ 2 + 1 ≤ wt t ξ := by unfold wt; linarith
  have hwpos : 0 < wt t ξ := wt_pos (by linarith) ξ
  have h2 : (1 + ‖ξ‖) ^ 2 ≤ 2 * wt t ξ := by nlinarith [sq_nonneg (1 - ‖ξ‖)]
  have h3 : (1 + ‖ξ‖) ^ 4 ≤ 4 * wt t ξ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h2 2
    nlinarith
  rw [Real.rpow_neg (by positivity), show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, inv_pow, inv_eq_one_div, ← div_eq_mul_inv,
    div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  nlinarith

lemma integrable_bound (hn : n ≤ 3) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin n) => 4 * (1 + ‖ξ‖) ^ (-4 : ℝ)) := by
  have hint := integrable_one_add_norm (E := EuclideanSpace ℝ (Fin n)) (μ := volume) (r := 4)
    (by rw [finrank_euclideanSpace_fin]; exact_mod_cast (by omega : n < 4))
  exact hint.const_mul 4

lemma integrable_wt_inv_sq (hn : n ≤ 3) {t : ℝ} (ht : 1 ≤ t) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin n) => (wt t ξ)⁻¹ ^ 2) := by
  refine (integrable_bound hn).mono' ?_ ?_
  · exact (((continuous_wt t).inv₀ fun ξ => (wt_pos (by linarith) ξ).ne').pow 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ξ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact wt_bound ht ξ

lemma tendsto_integral_wt (hn : n ≤ 3) :
    Tendsto (fun t : ℝ => ∫ ξ : EuclideanSpace ℝ (Fin n), (wt t ξ)⁻¹ ^ 2) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (F := fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) => (wt t ξ)⁻¹ ^ 2) (f := fun _ => 0)
    (fun ξ => 4 * (1 + ‖ξ‖) ^ (-4 : ℝ)) ?_ ?_ (integrable_bound hn) ?_
  · simpa using h
  · filter_upwards [eventually_ge_atTop 1] with t ht
    exact (((continuous_wt t).inv₀ fun ξ => (wt_pos (by linarith) ξ).ne').pow 2).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 1] with t ht
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact wt_bound ht ξ
  · refine Filter.Eventually.of_forall fun ξ => ?_
    have h1 : Tendsto (fun t : ℝ => wt t ξ) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_id
    have h2 := (tendsto_inv_atTop_zero.comp h1).pow 2
    simpa using h2

lemma L1_bound (G : L2 n) (hS : MemLp (fun ξ => laplaceSymbol n ξ * G ξ) 2 volume) {t : ℝ}
    (ht : 0 < t) (hI : Integrable (fun ξ : EuclideanSpace ℝ (Fin n) => (wt t ξ)⁻¹ ^ 2)) :
    Integrable (G : EuclideanSpace ℝ (Fin n) → ℂ) ∧
      ∫ ξ, ‖G ξ‖ ≤ Real.sqrt (∫ ξ : EuclideanSpace ℝ (Fin n), (wt t ξ)⁻¹ ^ 2) *
        (‖hS.toLp _‖ + t * ‖G‖) := by
  have hwpos : ∀ ξ : EuclideanSpace ℝ (Fin n), 0 < wt t ξ := wt_pos ht
  have hwc := continuous_wt (n := n) t
  have hwic : Continuous (fun ξ : EuclideanSpace ℝ (Fin n) => (wt t ξ)⁻¹) :=
    hwc.inv₀ (fun ξ => (hwpos ξ).ne')
  have hFr : MemLp (fun ξ : EuclideanSpace ℝ (Fin n) => (wt t ξ)⁻¹) 2 volume :=
    (memLp_two_iff_integrable_sq hwic.aestronglyMeasurable).mpr hI
  have hF : MemLp (fun ξ : EuclideanSpace ℝ (Fin n) => (((wt t ξ)⁻¹ : ℝ) : ℂ)) 2 volume :=
    hFr.ofReal
  have hsum : MemLp (fun ξ => laplaceSymbol n ξ * G ξ + (t : ℂ) • G ξ) 2 volume :=
    hS.add ((Lp.memLp G).const_smul (t : ℂ))
  have hpt : ∀ ξ, ‖(((wt t ξ * ‖G ξ‖ : ℝ)) : ℂ)‖ =
      ‖laplaceSymbol n ξ * G ξ + (t : ℂ) • G ξ‖ := by
    intro ξ
    have : laplaceSymbol n ξ * G ξ + (t : ℂ) • G ξ = ((wt t ξ : ℝ) : ℂ) * G ξ := by
      simp only [laplaceSymbol, wt, smul_eq_mul]
      push_cast
      ring
    rw [this, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (hwpos ξ), abs_mul, abs_of_pos (hwpos ξ), abs_norm]
  have hGt : MemLp (fun ξ => (((wt t ξ * ‖G ξ‖ : ℝ)) : ℂ)) 2 volume :=
    hsum.of_le (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hwc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable G).norm))
      (Filter.Eventually.of_forall fun ξ => (hpt ξ).le)
  set F := hF.toLp _ with hFdef
  set Gt := hGt.toLp _ with hGtdef
  have hpt2 : ∀ᵐ ξ ∂volume, (⟪(F : EuclideanSpace ℝ (Fin n) → ℂ) ξ,
      (Gt : EuclideanSpace ℝ (Fin n) → ℂ) ξ⟫_ℂ).re = ‖G ξ‖ := by
    filter_upwards [hF.coeFn_toLp, hGt.coeFn_toLp] with ξ h1 h2
    have := (hwpos ξ).ne'
    rw [h1, h2, re_inner_pt']
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero]
    field_simp
  have hintRe := (L2.integrable_inner (𝕜 := ℂ) F Gt).re
  have hGint : Integrable (fun ξ => ‖G ξ‖) := hintRe.congr hpt2
  have hGi : Integrable (G : EuclideanSpace ℝ (Fin n) → ℂ) :=
    (integrable_norm_iff (Lp.aestronglyMeasurable G)).mp hGint
  refine ⟨hGi, ?_⟩
  have hinner : (⟪F, Gt⟫_ℂ).re = ∫ ξ, ‖G ξ‖ := by
    rw [L2.inner_def, ← integral_congr_ae hpt2]
    exact (integral_re (L2.integrable_inner (𝕜 := ℂ) F Gt)).symm
  have hFn : ‖F‖ ≤ Real.sqrt (∫ ξ : EuclideanSpace ℝ (Fin n), (wt t ξ)⁻¹ ^ 2) := by
    have hsq : ‖F‖ ^ 2 = ∫ ξ : EuclideanSpace ℝ (Fin n), (wt t ξ)⁻¹ ^ 2 := by
      rw [show ‖F‖ ^ 2 = (⟪F, F⟫_ℂ).re by simpa using (norm_sq_eq_re_inner (𝕜 := ℂ) F),
        L2.inner_def]
      rw [show (∫ a, ⟪(F : EuclideanSpace ℝ (Fin n) → ℂ) a, (F : EuclideanSpace ℝ (Fin n) → ℂ) a⟫_ℂ).re
        = ∫ a, (⟪(F : EuclideanSpace ℝ (Fin n) → ℂ) a, (F : EuclideanSpace ℝ (Fin n) → ℂ) a⟫_ℂ).re
        from (integral_re (L2.integrable_inner (𝕜 := ℂ) F F)).symm]
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp] with ξ h
      rw [h, re_inner_pt']
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero]
      ring
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  have hGtn : ‖Gt‖ ≤ ‖hS.toLp _‖ + t * ‖G‖ := by
    calc ‖Gt‖ ≤ ‖hS.toLp _ + (t : ℂ) • G‖ := by
          apply Lp.norm_le_norm_of_ae_le
          filter_upwards [hGt.coeFn_toLp, Lp.coeFn_add (hS.toLp _) ((t : ℂ) • G),
            hS.coeFn_toLp, Lp.coeFn_smul (t : ℂ) G] with ξ h1 h2 h3 h4
          rw [h1, h2, Pi.add_apply, h3, h4, Pi.smul_apply]
          exact (hpt ξ).le
      _ ≤ ‖hS.toLp _‖ + ‖(t : ℂ) • G‖ := norm_add_le _ _
      _ = ‖hS.toLp _‖ + t * ‖G‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  calc ∫ ξ, ‖G ξ‖ = (⟪F, Gt⟫_ℂ).re := hinner.symm
    _ ≤ ‖F‖ * ‖Gt‖ := by simpa using re_inner_le_norm (𝕜 := ℂ) F Gt
    _ ≤ _ := mul_le_mul hFn hGtn (norm_nonneg _) (Real.sqrt_nonneg _)

end SobAux

open SobAux in
theorem solution (n : ℕ) (hn : n ≤ 3) :
    (∀ ψ ∈ sobolevH2 n, ∃ f : EuclideanSpace ℝ (Fin n) →C₀ ℂ,
        (ψ : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume] f) ∧
      ∀ a : ℝ, 0 < a → ∃ b : ℝ, 0 < b ∧
        ∀ (ψ : (freeHamiltonian n).domain) (f : EuclideanSpace ℝ (Fin n) →C₀ ℂ),
          ((ψ : L2 n) : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume] f →
            ‖f‖ ≤ a * ‖freeHamiltonian n ψ‖ + b * ‖(ψ : L2 n)‖ := by
  have hI1 := integrable_wt_inv_sq (n := n) hn (le_refl (1 : ℝ))
  have hrep : ∀ ψ : L2 n, ψ ∈ sobolevH2 n → ∃ hG : Integrable ((fourierL2 n ψ : L2 n) :
      EuclideanSpace ℝ (Fin n) → ℂ), (ψ : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume]
        ⇑(c0OfL1 ((fourierL2 n ψ : L2 n) : EuclideanSpace ℝ (Fin n) → ℂ) hG) := by
    intro ψ hψ
    have hS : MemLp (fun ξ => laplaceSymbol n ξ * (fourierL2 n ψ : L2 n) ξ) 2 volume := hψ
    obtain ⟨hG, -⟩ := L1_bound (fourierL2 n ψ) hS (t := 1) one_pos hI1
    refine ⟨hG, ?_⟩
    have h1 : ψ = 𝓕⁻ (fourierL2 n ψ) := ((fourierL2 n).symm_apply_apply ψ).symm
    have := fourierInv_L2_ae_eq (fourierL2 n ψ) hG
    rw [coe_c0OfL1]
    conv_lhs => rw [h1]
    exact this
  refine ⟨fun ψ hψ => ?_, ?_⟩
  · obtain ⟨hG, h⟩ := hrep ψ hψ
    exact ⟨_, h⟩
  · intro a ha
    have hlim := tendsto_integral_wt (n := n) hn
    obtain ⟨t, ht1, hta⟩ : ∃ t : ℝ, 1 ≤ t ∧
        ∫ ξ : EuclideanSpace ℝ (Fin n), (wt t ξ)⁻¹ ^ 2 ≤ a ^ 2 := by
      obtain ⟨t, h1, h2⟩ :=
        ((hlim.eventually (ge_mem_nhds (pow_pos ha 2))).and (eventually_ge_atTop 1)).exists
      exact ⟨t, h2, h1⟩
    set c := Real.sqrt (∫ ξ : EuclideanSpace ℝ (Fin n), (wt t ξ)⁻¹ ^ 2) with hcdef
    have hc : c ≤ a := Real.sqrt_le_iff.mpr ⟨ha.le, hta⟩
    have hc0 : 0 ≤ c := Real.sqrt_nonneg _
    refine ⟨c * t + 1, by positivity, ?_⟩
    intro ψ f hf
    have hψ : (ψ : L2 n) ∈ sobolevH2 n := ψ.2
    have hS : MemLp (fun ξ => laplaceSymbol n ξ * (fourierL2 n ψ : L2 n) ξ) 2 volume := hψ
    obtain ⟨hG, hrep'⟩ := hrep ψ hψ
    obtain ⟨-, hb⟩ := L1_bound (fourierL2 n ψ) hS (t := t) (by linarith)
      (integrable_wt_inv_sq (n := n) hn ht1)
    have hfeq : f = c0OfL1 ((fourierL2 n ψ : L2 n) : EuclideanSpace ℝ (Fin n) → ℂ) hG := by
      have : (f : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume] c0OfL1 ((fourierL2 n ψ : L2 n) : EuclideanSpace ℝ (Fin n) → ℂ) hG := hf.symm.trans hrep'
      exact DFunLike.ext' ((Continuous.ae_eq_iff_eq volume f.continuous
        (c0OfL1 ((fourierL2 n ψ : L2 n) : EuclideanSpace ℝ (Fin n) → ℂ) hG).continuous).mp this)
    have hnormH : ‖freeHamiltonian n ψ‖ = ‖hS.toLp _‖ := by
      change ‖(fourierL2 n).symm _‖ = _
      rw [LinearIsometryEquiv.norm_map]
      rfl
    have hnormψ : ‖fourierL2 n ψ‖ = ‖(ψ : L2 n)‖ := LinearIsometryEquiv.norm_map _ _
    calc ‖f‖ = ‖c0OfL1 ((fourierL2 n ψ : L2 n) : EuclideanSpace ℝ (Fin n) → ℂ) hG‖ := by rw [hfeq]
      _ ≤ ∫ ξ, ‖(fourierL2 n ψ : L2 n) ξ‖ := norm_c0OfL1_le _ hG
      _ ≤ c * (‖hS.toLp _‖ + t * ‖fourierL2 n ψ‖) := hb
      _ ≤ a * ‖freeHamiltonian n ψ‖ + (c * t + 1) * ‖(ψ : L2 n)‖ := by
        rw [hnormH, hnormψ]
        have h1 := mul_le_mul_of_nonneg_right hc (norm_nonneg (hS.toLp _))
        have h2 := norm_nonneg (ψ : L2 n)
        nlinarith
