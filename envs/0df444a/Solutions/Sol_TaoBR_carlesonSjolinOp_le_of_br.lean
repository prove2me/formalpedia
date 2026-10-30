-- Prove2me | solution 1 for TaoBR.carlesonSjolinOp_le_of_br
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:49:28.304444+00:00
-- url     : https://prove2.me/submissions/ea6c46eb-999e-4835-af31-7bf1feb1d0dd

import Mathlib
import Definitions.Def_TaoBR
import Theorems.Thm_TaoBR_opNorm_le_of_contDiff

/-! Helper lemmas on kernel operators, copied from the Theorem 1.1 development. -/

open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace

namespace TaoBR
namespace CS

variable {n : ℕ}

lemma eLpNorm_comp_smul (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (g : E n → ℂ) (R : ℝ)
    (hR : 0 < R) :
    eLpNorm (fun y => g (R • y)) p volume =
      ENNReal.ofReal (R ^ (-((n : ℝ) / p.toReal))) * eLpNorm g p volume := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  have hmap := Measure.map_addHaar_smul (volume : Measure (E n)) hR.ne'
  have h1 : ∫⁻ x, ‖g (R • x)‖ₑ ^ p.toReal =
      ENNReal.ofReal (|(R ^ Module.finrank ℝ (E n))⁻¹|) * ∫⁻ x, ‖g x‖ₑ ^ p.toReal := by
    rw [← smul_eq_mul, ← lintegral_smul_measure, ← hmap]
    exact (lintegral_map_equiv (fun x => ‖g x‖ₑ ^ p.toReal) (MeasurableEquiv.smul₀ R hR.ne')).symm
  rw [h1, finrank_euclideanSpace_fin, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  congr 2
  rw [abs_of_pos (by positivity), ← Real.rpow_natCast, ← Real.rpow_neg hR.le,
    ← Real.rpow_mul hR.le]
  congr 1; field_simp

lemma kernelOp_aesm (k : E n → E n → ℂ) (hk : Continuous (Function.uncurry k)) (u : E n → ℂ)
    (hu : AEStronglyMeasurable u volume) : AEStronglyMeasurable (kernelOp k u) volume := by
  have h : AEStronglyMeasurable (fun z : E n × E n => k z.1 z.2 * u z.2)
      ((volume : Measure (E n)).prod volume) :=
    hk.aestronglyMeasurable.mul hu.comp_snd
  exact h.integral_prod_right'

lemma kernelOp_integrable (p : ℝ≥0∞) (hp : 1 ≤ p) (k : E n → E n → ℂ)
    (hk : Continuous (Function.uncurry k)) (M A : ℝ) (hM : ∀ x y, ‖k x y‖ ≤ M)
    (hA : ∀ x y, k x y ≠ 0 → ‖x‖ ≤ A ∧ ‖y‖ ≤ A) (u : E n → ℂ) (hu : MemLp u p volume)
    (x : E n) : Integrable (fun y => k x y * u y) volume := by
  haveI : IsFiniteMeasure (volume.restrict (closedBall (0 : E n) A)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have hu1 : Integrable u (volume.restrict (closedBall (0 : E n) A)) :=
    (hu.restrict _).integrable hp
  have hk1 : Continuous (k x) := hk.comp (Continuous.prodMk_right x)
  have h2 : IntegrableOn (fun y => k x y * u y) (closedBall (0 : E n) A) volume :=
    hu1.bdd_mul hk1.aestronglyMeasurable.restrict (ae_of_all _ (hM x))
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h2
  intro y hy
  have : k x y ≠ 0 := left_ne_zero_of_mul hy
  simpa using (hA x y this).2

lemma kernelOp_bound (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤) (k : E n → E n → ℂ)
    (hk : Continuous (Function.uncurry k)) (M A : ℝ) (hM : ∀ x y, ‖k x y‖ ≤ M)
    (hA : ∀ x y, k x y ≠ 0 → ‖x‖ ≤ A ∧ ‖y‖ ≤ A) (u : E n → ℂ) (hu : MemLp u p volume) :
    eLpNorm (kernelOp k u) p volume ≤
      (ENNReal.ofReal M * volume (closedBall (0 : E n) A) ^ (1 - 1 / p.toReal) *
        volume (closedBall (0 : E n) A) ^ (1 / p.toReal)) * eLpNorm u p volume := by
  set B := closedBall (0 : E n) A
  have hp1 : 1 ≤ p.toReal := by
    have := (ENNReal.toReal_le_toReal (by simp) hpt).2 hp; simpa using this
  set c : ℝ≥0∞ := ENNReal.ofReal M * (eLpNorm u p volume * volume B ^ (1 - 1 / p.toReal))
  have hct : c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
    hu.eLpNorm_ne_top (ENNReal.rpow_ne_top_of_nonneg (by
      have : 1 / p.toReal ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
      linarith) measure_closedBall_lt_top.ne))
  have hpt' : ∀ x, ‖kernelOp k u x‖ₑ ≤ ‖B.indicator (fun _ => c.toReal) x‖ₑ := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hct]
      calc ‖kernelOp k u x‖ₑ ≤ ∫⁻ y, ‖k x y * u y‖ₑ := enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ y, B.indicator (fun y => ENNReal.ofReal M * ‖u y‖ₑ) y := by
          apply lintegral_mono; intro y
          by_cases hy : y ∈ B
          · rw [Set.indicator_of_mem hy]
            show ‖k x y * u y‖ₑ ≤ _
            rw [enorm_mul]
            gcongr
            rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal (hM x y)
          · rw [Set.indicator_of_notMem hy]
            have : k x y = 0 := by
              by_contra h; exact hy (by simpa [B] using (hA x y h).2)
            simp [this]
        _ = ENNReal.ofReal M * ∫⁻ y in B, ‖u y‖ₑ := by
          rw [lintegral_indicator measurableSet_closedBall, lintegral_const_mul' _ _
            ENNReal.ofReal_ne_top]
        _ ≤ c := by
          simp only [c]
          gcongr
          have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict B)
            (p := 1) (q := p) hp hu.aestronglyMeasurable.restrict
          rw [eLpNorm_one_eq_lintegral_enorm, Measure.restrict_apply_univ] at h1
          refine h1.trans ?_
          simp only [ENNReal.toReal_one, div_one]
          gcongr
          exact Measure.restrict_le_self
    · have : kernelOp k u x = 0 := by
        simp only [kernelOp]
        apply integral_eq_zero_of_ae; apply ae_of_all; intro y
        have : k x y = 0 := by
          by_contra h; exact hx (by simpa [B] using (hA x y h).1)
        simp [this]
      simp [this]
  refine (eLpNorm_mono_enorm hpt').trans ((eLpNorm_indicator_const_le _ p).trans ?_)
  rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hct]
  simp only [c]
  apply le_of_eq; ring

/-- Density: a bound on Schwartz functions for a bounded compactly supported kernel extends
to the operator norm. -/
lemma opNorm_le_of_schwartz (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤) (k : E n → E n → ℂ)
    (hk : Continuous (Function.uncurry k)) (M A : ℝ) (hM : ∀ x y, ‖k x y‖ ≤ M)
    (hA : ∀ x y, k x y ≠ 0 → ‖x‖ ≤ A ∧ ‖y‖ ≤ A) (D : ℝ≥0∞) (hDt : D ≠ ⊤)
    (hD : ∀ g : 𝓢(E n, ℂ), eLpNorm (kernelOp k g) p volume ≤ D * eLpNorm g p volume) :
    opNorm p p (kernelOp k) ≤ D := by
  apply sInf_le
  intro f hf
  set L : ℝ≥0∞ := ENNReal.ofReal M * volume (closedBall (0 : E n) A) ^ (1 - 1 / p.toReal) *
        volume (closedBall (0 : E n) A) ^ (1 / p.toReal) with hL
  have hp1 : 1 ≤ p.toReal := by
    have := (ENNReal.toReal_le_toReal (by simp) hpt).2 hp; simpa using this
  have hLt : L ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg ?_ measure_closedBall_lt_top.ne))
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) measure_closedBall_lt_top.ne)
    have : 1 / p.toReal ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
    linarith
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set δ : ℝ := ε / (D.toReal + L.toReal + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨g, hg1, hg2, hg3⟩ := hf.exist_eLpNorm_sub_le hpt hp hδ0
  set gs : 𝓢(E n, ℂ) := hg1.toSchwartzMap hg2
  have hgs : (gs : E n → ℂ) = g := rfl
  have hgm : MemLp g p volume := hgs ▸ gs.memLp p volume
  have hfg : MemLp (f - g) p volume := hf.sub hgm
  have hsplit : kernelOp k f = kernelOp k g + kernelOp k (f - g) := by
    funext x
    simp only [kernelOp, Pi.add_apply, Pi.sub_apply, mul_sub]
    rw [← integral_add (kernelOp_integrable p hp k hk M A hM hA g hgm x)]
    · congr 1; funext y; ring
    · exact (kernelOp_integrable p hp k hk M A hM hA f hf x).sub
        (kernelOp_integrable p hp k hk M A hM hA g hgm x)
  have h1 : eLpNorm (kernelOp k f) p volume ≤ D * eLpNorm g p volume + L * ENNReal.ofReal δ := by
    rw [hsplit]
    refine (eLpNorm_add_le (kernelOp_aesm k hk g hgm.1) (kernelOp_aesm k hk _ hfg.1) hp).trans ?_
    gcongr
    · exact hD gs
    · exact (kernelOp_bound p hp hpt k hk M A hM hA _ hfg).trans (by gcongr)
  have h2 : eLpNorm g p volume ≤ eLpNorm f p volume + ENNReal.ofReal δ := by
    have : g = f - (f - g) := by abel
    rw [this]
    exact (eLpNorm_sub_le hf.1 hfg.1 hp).trans (by gcongr)
  calc eLpNorm (kernelOp k f) p volume
      ≤ D * (eLpNorm f p volume + ENNReal.ofReal δ) + L * ENNReal.ofReal δ :=
        h1.trans (by gcongr)
    _ = D * eLpNorm f p volume + (D + L) * ENNReal.ofReal δ := by ring
    _ ≤ D * eLpNorm f p volume + ε := by
        gcongr
        rw [← ENNReal.ofReal_toReal hDt, ← ENNReal.ofReal_toReal hLt,
          ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal]
        apply ENNReal.ofReal_le_ofReal
        rw [hδ, mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ ε := ε.2
        nlinarith [ENNReal.toReal_nonneg (a := D), ENNReal.toReal_nonneg (a := L)]


lemma eLpNorm_le_opNorm {p : ℝ≥0∞} {T : (E n → ℂ) → (E n → ℂ)} {D : ℝ≥0∞}
    (hT : opNorm p p T ≤ D) (hD : D ≠ ⊤) (h0 : T 0 = 0) {f : E n → ℂ} (hf : MemLp f p volume) :
    eLpNorm (T f) p volume ≤ D * eLpNorm f p volume := by
  have hlt : sInf {C : ℝ≥0∞ | ∀ f : E n → ℂ, MemLp f p volume →
      eLpNorm (T f) p volume ≤ C * eLpNorm f p volume} < ⊤ := lt_of_le_of_lt hT (lt_top_iff_ne_top.2 hD)
  obtain ⟨C₁, hC₁, -⟩ := sInf_lt_iff.1 hlt
  by_cases hz : eLpNorm f p volume = 0
  · have := hC₁ f hf; rw [hz, mul_zero] at this; rw [hz, mul_zero]; exact this
  have hft : eLpNorm f p volume ≠ ⊤ := hf.eLpNorm_ne_top
  have : eLpNorm (T f) p volume / eLpNorm f p volume ≤ opNorm p p T := by
    apply le_sInf
    intro C hC
    exact (ENNReal.div_le_iff hz hft).2 (hC f hf)
  exact (ENNReal.div_le_iff hz hft).1 (this.trans hT)


end CS
end TaoBR


section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR
namespace CS
variable {n : ℕ}
/-!
# Tao 1999, p. 3: the Carleson–Sjölin reduction `BR(p, α) ⇒ ‖G_R f‖_p ≲ R^{-n/p'+α} ‖f‖_p`

Route.
* (K) `S^δ g = K_δ * g` for Schwartz `g`, `K_δ = 𝓕⁻ m_δ`; by scaling, `BR` bounds the dilated
  kernel operators `g ↦ ∫ Rⁿ K_δ(R(x - y)) g(y) dy` uniformly in `R`.
* (R) `K_δ(z) = c · I(|z|)` with `I(r) = ∫_{-1}^1 e^{2πirt} (1 - t²)^μ dt`, `μ = δ + (n-1)/2`.
* (C) Contour deformation (Hankel form): `I(r) = r^{-μ-1} (e^{2πir} A(1/r) + e^{-2πir} conj A(1/r))`
  with `A(τ) = -i ∫_0^∞ e^{-2πu} u^μ (τu - 2i)^μ du`.
* (A) `A` is smooth on all of `ℝ` and `A(0) ≠ 0`.
* (P) For a piece `ψ` supported in `B(x₀, r) × B(y₀, r)`, `|x₀ - y₀| ≥ 6r`: the localized dilated
  kernels at scales `R` and `R + h` combine, with smooth amplitudes in `(x, 1/R)` and Lemma 2.1,
  to the kernel `e^{2πiR|x-y|} ψ(x, y)` (two frequencies separate `e^{+}` from `e^{-}`).
* (U) A smooth partition of unity splits a general `ψ` into such pieces.
-/
/-- The Bochner–Riesz kernel `K_δ = 𝓕⁻ m_δ`. -/
noncomputable def Kfun (n : ℕ) (δ : ℝ) : E n → ℂ :=
  𝓕⁻ (fun ξ : E n => (brSymbol δ ξ : ℂ))

/-- `I(r) = ∫_{-1}^{1} e^{2πirt} (1 - t²)^μ dt`. -/
noncomputable def I1 (μ r : ℝ) : ℂ :=
  ∫ t in (-1 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * ((r * t : ℝ) : ℂ)) *
    (((1 - t ^ 2) ^ μ : ℝ) : ℂ)

/-- The Hankel amplitude `A(τ) = -i ∫_0^∞ e^{-2πu} u^μ (τu - 2i)^μ du`. -/
noncomputable def Aμ (μ τ : ℝ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ), -Complex.I * ((Real.exp (-2 * Real.pi * u) * u ^ μ : ℝ) : ℂ) *
    (((τ * u : ℝ) : ℂ) - 2 * Complex.I) ^ (μ : ℂ)

end CS
end TaoBR
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR.CS.PartK
variable {n : ℕ}
lemma plusPow_measurable (δ : ℝ) : Measurable (fun t : ℝ => plusPow δ t) := by
  unfold plusPow
  exact Measurable.ite measurableSet_Ioi (measurable_id.pow_const δ) measurable_const

lemma plusPow_nonneg (δ t : ℝ) : 0 ≤ plusPow δ t := by
  unfold plusPow; split_ifs with h
  · exact Real.rpow_nonneg h.le _
  · exact le_rfl

lemma plusPow_le_one (δ t : ℝ) (hδ : 0 ≤ δ) (ht : t ≤ 1) : plusPow δ t ≤ 1 := by
  unfold plusPow; split_ifs with h
  · exact Real.rpow_le_one h.le ht hδ
  · exact zero_le_one

lemma plusPow_eq_zero (δ t : ℝ) (ht : t ≤ 0) : plusPow δ t = 0 := by
  unfold plusPow; rw [if_neg (not_lt.2 ht)]

lemma plusPow_mul (δ s u : ℝ) (hs : 0 < s) : plusPow δ (s * u) = s ^ δ * plusPow δ u := by
  unfold plusPow
  by_cases hu : 0 < u
  · rw [if_pos (mul_pos hs hu), if_pos hu, Real.mul_rpow hs.le hu.le]
  · rw [if_neg hu, if_neg, mul_zero]
    intro h; exact hu (pos_of_mul_pos_right h hs.le)

/-- Integrability from a bound and a support of finite measure. -/
lemma integrable_of_bdd {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    {μ : Measure X} (f : X → F)
    (hf : AEStronglyMeasurable f μ) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) (s : Set X)
    (_hsm : MeasurableSet s) (hs : μ s < ⊤) (hsupp : ∀ x, f x ≠ 0 → x ∈ s) : Integrable f μ := by
  have h1 : IntegrableOn f s μ :=
    Measure.integrableOn_of_bounded hs.ne hf (ae_of_all _ hb)
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h1
  intro x hx; exact hsupp x hx

lemma brSymbol_measurable (δ : ℝ) : Measurable (fun ξ : E n => brSymbol δ ξ) := by
  unfold brSymbol
  exact (plusPow_measurable δ).comp (by fun_prop)

lemma brSymbol_norm_le (δ : ℝ) (hδ : 0 ≤ δ) (ξ : E n) : ‖(brSymbol δ ξ : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, brSymbol, abs_of_nonneg (plusPow_nonneg _ _)]
  exact plusPow_le_one _ _ hδ (by nlinarith [norm_nonneg ξ])

lemma brSymbol_supp (δ : ℝ) (ξ : E n) (h : (brSymbol δ ξ : ℂ) ≠ 0) :
    ξ ∈ closedBall (0 : E n) 1 := by
  rw [mem_closedBall, dist_zero_right]
  by_contra hc
  push Not at hc
  apply h
  unfold brSymbol
  rw [plusPow_eq_zero _ _ (by nlinarith), Complex.ofReal_zero]

lemma brSymbol_integrable (δ : ℝ) (hδ : 0 ≤ δ) :
    Integrable (fun ξ : E n => (brSymbol δ ξ : ℂ)) volume :=
  integrable_of_bdd _ (Complex.measurable_ofReal.comp (brSymbol_measurable δ)).aestronglyMeasurable
    1 (brSymbol_norm_le δ hδ) _ measurableSet_closedBall measure_closedBall_lt_top
    (brSymbol_supp δ)

theorem bochnerRiesz_eq_kernel (δ : ℝ) (hδ : 0 ≤ δ) (g : 𝓢(E n, ℂ)) (x : E n) :
    bochnerRiesz δ (g : E n → ℂ) x = ∫ y, Kfun n δ (x - y) * g y := by
  have hm := brSymbol_integrable (n := n) δ hδ
  have hmm : Measurable (fun ξ : E n => (brSymbol δ ξ : ℂ)) :=
    Complex.measurable_ofReal.comp (brSymbol_measurable δ)
  have hg : Integrable (g : E n → ℂ) volume := g.integrable
  simp only [bochnerRiesz, multiplier, Kfun, Real.fourierInv_eq', Real.fourier_eq', smul_eq_mul]
  set F : E n → E n → ℂ := fun ξ y =>
    Complex.exp (↑(2 * Real.pi * ⟪ξ, x⟫) * Complex.I) * (brSymbol δ ξ : ℂ) *
      (Complex.exp (↑(-2 * Real.pi * ⟪y, ξ⟫) * Complex.I) * g y) with hF
  have hint : Integrable (Function.uncurry F) ((volume : Measure (E n)).prod volume) := by
    refine Integrable.mono' (hm.norm.mul_prod hg.norm) ?_ ?_
    · apply Measurable.aestronglyMeasurable
      simp only [hF, Function.uncurry_def]
      have : Measurable (fun p : E n × E n => (g p.2 : ℂ)) := g.continuous.measurable.comp measurable_snd
      have h2 : Measurable (fun p : E n × E n => (brSymbol δ p.1 : ℂ)) :=
        hmm.comp measurable_fst
      fun_prop
    · refine ae_of_all _ fun p => ?_
      simp only [hF, Function.uncurry_def, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact le_rfl
  have h1 : ∀ ξ, Complex.exp (↑(2 * Real.pi * ⟪ξ, x⟫) * Complex.I) *
      ((brSymbol δ ξ : ℂ) * ∫ y, Complex.exp (↑(-2 * Real.pi * ⟪y, ξ⟫) * Complex.I) * g y) =
      ∫ y, F ξ y := by
    intro ξ
    simp only [hF]
    rw [← integral_const_mul, ← integral_const_mul]; congr 1; funext y; ring
  simp_rw [h1]
  rw [integral_integral_swap hint]
  congr 1; funext y
  rw [← integral_mul_const]
  congr 1; funext ξ
  simp only [hF]
  have : Complex.exp (↑(2 * Real.pi * ⟪ξ, x⟫) * Complex.I) *
      Complex.exp (↑(-2 * Real.pi * ⟪y, ξ⟫) * Complex.I) =
      Complex.exp (↑(2 * Real.pi * ⟪ξ, x - y⟫) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1
    rw [inner_sub_right, real_inner_comm y ξ]; push_cast; ring
  rw [← this]; ring

end TaoBR.CS.PartK
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR
namespace CS
variable {n : ℕ}
/-! ## Part K: the kernel of `S^δ` and its dilates -/

end CS
end TaoBR
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR.CS.PartK
variable {n : ℕ}
lemma Kfun_eq_fourierIntegral (δ : ℝ) :
    Kfun n δ = VectorFourier.fourierIntegral Real.fourierChar volume (-innerₗ (E n))
      (fun ξ : E n => (brSymbol δ ξ : ℂ)) := rfl

theorem Kfun_continuous (δ : ℝ) (hδ : 0 ≤ δ) : Continuous (Kfun n δ) := by
  rw [Kfun_eq_fourierIntegral]
  refine VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar ?_
    (brSymbol_integrable δ hδ)
  simp only [LinearMap.neg_apply, innerₗ_apply_apply]
  fun_prop

end TaoBR.CS.PartK
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR
namespace CS
variable {n : ℕ}
alias Kfun_continuous := TaoBR.CS.PartK.Kfun_continuous

end CS
end TaoBR
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR.CS.PartK
variable {n : ℕ}

end TaoBR.CS.PartK
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR
namespace CS
variable {n : ℕ}

end CS
end TaoBR
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR.CS.PartK
variable {n : ℕ}
/-- `BR` bounds the dilated kernel operators uniformly in the scale. -/
theorem dil_bound (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤) (δ : ℝ) (hδ : 0 ≤ δ) (A : ℝ≥0)
    (hA : ∀ f : 𝓢(E n, ℂ), eLpNorm (bochnerRiesz δ (f : E n → ℂ)) p volume ≤
      A * eLpNorm f p volume)
    (R : ℝ) (hR : 0 < R) (g : 𝓢(E n, ℂ)) :
    eLpNorm (fun x => ∫ y, ((R ^ n : ℝ) : ℂ) * Kfun n δ (R • (x - y)) * g y) p volume ≤
      A * eLpNorm g p volume := by
  set e : E n ≃L[ℝ] E n :=
    (LinearEquiv.smulOfNeZero ℝ (E n) R⁻¹ (inv_ne_zero hR.ne')).toContinuousLinearEquiv
  set h : 𝓢(E n, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e g
  have hh : ∀ y, h y = g (R⁻¹ • y) := fun y => rfl
  have key : ∀ x, (∫ y, ((R ^ n : ℝ) : ℂ) * Kfun n δ (R • (x - y)) * g y) =
      bochnerRiesz δ (h : E n → ℂ) (R • x) := by
    intro x
    rw [bochnerRiesz_eq_kernel δ hδ h]
    have hc := Measure.integral_comp_smul (μ := (volume : Measure (E n)))
      (fun y' => Kfun n δ (R • x - y') * h y') R
    rw [finrank_euclideanSpace_fin] at hc
    calc (∫ y, ((R ^ n : ℝ) : ℂ) * Kfun n δ (R • (x - y)) * g y)
        = ((R ^ n : ℝ) : ℂ) * ∫ y, Kfun n δ (R • x - R • y) * h (R • y) := by
          rw [← integral_const_mul]; congr 1; funext y
          rw [hh, smul_sub, inv_smul_smul₀ hR.ne']; ring
      _ = ((R ^ n : ℝ) : ℂ) * (|(R ^ n)⁻¹| • ∫ y', Kfun n δ (R • x - y') * h y') := by
          rw [hc]
      _ = ∫ y', Kfun n δ (R • x - y') * h y' := by
          rw [abs_of_pos (by positivity), Complex.real_smul, ← mul_assoc]
          push_cast
          rw [mul_inv_cancel₀ (by exact_mod_cast (pow_pos hR n).ne'), one_mul]
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp).ne'
  have hfun : (fun x => ∫ y, ((R ^ n : ℝ) : ℂ) * Kfun n δ (R • (x - y)) * g y) =
      fun x => bochnerRiesz δ (h : E n → ℂ) (R • x) := funext key
  have hg : (g : E n → ℂ) = fun y => h (R • y) := by
    funext y; rw [hh, inv_smul_smul₀ hR.ne']
  rw [hfun, eLpNorm_comp_smul p hp0 hpt _ R hR]
  conv_rhs => rw [hg, eLpNorm_comp_smul p hp0 hpt _ R hR]
  calc ENNReal.ofReal (R ^ (-((n : ℝ) / p.toReal))) * eLpNorm (bochnerRiesz δ (h : E n → ℂ)) p volume
      ≤ ENNReal.ofReal (R ^ (-((n : ℝ) / p.toReal))) * (A * eLpNorm h p volume) := by
        gcongr; exact hA h
    _ = _ := by ring

end TaoBR.CS.PartK
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR
namespace CS
variable {n : ℕ}
alias dil_bound := TaoBR.CS.PartK.dil_bound

end CS
end TaoBR
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR.CS.PartK
variable {n : ℕ}
/-! ## Part R -/
lemma Kfun_isometry (δ : ℝ) (A : E n ≃ₗᵢ[ℝ] E n) (z : E n) : Kfun n δ (A z) = Kfun n δ z := by
  rw [Kfun, ← Real.fourierInv_comp_linearIsometry]
  have : (fun ξ : E n => (brSymbol δ ξ : ℂ)) ∘ A = fun ξ : E n => (brSymbol δ ξ : ℂ) := by
    funext ξ; simp [brSymbol, A.norm_map]
  rw [this]

/-- The inner integral over the orthogonal directions. -/
lemma inner_integral (k : ℕ) (δ s : ℝ) :
    ∫ η : Fin k → ℝ, plusPow δ (s - ∑ i, η i ^ 2) =
      (∫ η : Fin k → ℝ, plusPow δ (1 - ∑ i, η i ^ 2)) * plusPow (δ + (k : ℝ) / 2) s := by
  rcases le_or_gt s 0 with hs | hs
  · rw [plusPow_eq_zero _ _ hs, mul_zero]
    apply integral_eq_zero_of_ae; apply ae_of_all; intro η
    apply plusPow_eq_zero
    have : 0 ≤ ∑ i, η i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  · have hc := Measure.integral_comp_smul (μ := (volume : Measure (Fin k → ℝ)))
      (fun η => plusPow δ (s - ∑ i, η i ^ 2)) (Real.sqrt s)
    rw [Module.finrank_fin_fun] at hc
    have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
    have h1 : ∀ η : Fin k → ℝ, plusPow δ (s - ∑ i, (Real.sqrt s • η) i ^ 2) =
        s ^ δ * plusPow δ (1 - ∑ i, η i ^ 2) := by
      intro η
      rw [← plusPow_mul _ _ _ hs]
      congr 1
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, hsq, ← Finset.mul_sum]
      ring
    simp only [h1] at hc
    rw [integral_const_mul] at hc
    have hpos : 0 < Real.sqrt s ^ k := pow_pos (Real.sqrt_pos.2 hs) k
    rw [abs_of_pos (inv_pos.2 hpos), smul_eq_mul] at hc
    have hpp : plusPow (δ + (k : ℝ) / 2) s = s ^ δ * Real.sqrt s ^ k := by
      rw [plusPow, if_pos hs, Real.rpow_add hs, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
        ← Real.rpow_mul hs.le]
      ring_nf
    rw [hpp]
    field_simp at hc
    linear_combination -hc

lemma c0_pos (k : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    0 < ∫ η : Fin k → ℝ, plusPow δ (1 - ∑ i, η i ^ 2) := by
  have hmeas : Measurable (fun η : Fin k → ℝ => plusPow δ (1 - ∑ i, η i ^ 2)) :=
    (plusPow_measurable δ).comp (by fun_prop)
  have hint : Integrable (fun η : Fin k → ℝ => plusPow δ (1 - ∑ i, η i ^ 2)) volume := by
    refine integrable_of_bdd _ hmeas.aestronglyMeasurable 1 ?_ (closedBall 0 1)
      measurableSet_closedBall measure_closedBall_lt_top ?_
    · intro η
      rw [Real.norm_eq_abs, abs_of_nonneg (plusPow_nonneg _ _)]
      exact plusPow_le_one _ _ hδ (by
        have : 0 ≤ ∑ i, η i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
        linarith)
    · intro η hη
      have h1 : ∑ i, η i ^ 2 < 1 := by
        by_contra hc; exact hη (plusPow_eq_zero _ _ (by linarith))
      rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have : η i ^ 2 ≤ ∑ j, η j ^ 2 :=
        Finset.single_le_sum (f := fun j => η j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [Real.norm_eq_abs, abs_le]; constructor <;> nlinarith
  rw [integral_pos_iff_support_of_nonneg (fun η => plusPow_nonneg _ _) hint]
  have hU : IsOpen {η : Fin k → ℝ | ∑ i, η i ^ 2 < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hsub : {η : Fin k → ℝ | ∑ i, η i ^ 2 < 1} ⊆
      Function.support (fun η : Fin k → ℝ => plusPow δ (1 - ∑ i, η i ^ 2)) := by
    intro η hη
    simp only [Set.mem_ofPred_eq] at hη
    simp only [Function.mem_support, plusPow, if_pos (sub_pos.2 hη)]
    exact (Real.rpow_pos_of_pos (sub_pos.2 hη) _).ne'
  exact lt_of_lt_of_le (hU.measure_pos volume ⟨0, by simp⟩) (measure_mono hsub)

lemma Kfun_axis (k : ℕ) (hk : 1 ≤ k) (δ r : ℝ) (hδ : 0 ≤ δ) :
    Kfun (k + 1) δ (r • EuclideanSpace.single (0 : Fin (k + 1)) (1 : ℝ)) =
      ((∫ η : Fin k → ℝ, plusPow δ (1 - ∑ i, η i ^ 2) : ℝ) : ℂ) * I1 (δ + (k : ℝ) / 2) r := by
  set c0 : ℝ := ∫ η : Fin k → ℝ, plusPow δ (1 - ∑ i, η i ^ 2) with hc0
  set μ : ℝ := δ + (k : ℝ) / 2 with hμ
  have hμpos : 0 < μ := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [hμ]; linarith
  set G : (Fin (k + 1) → ℝ) → ℂ := fun x =>
    Complex.exp (2 * Real.pi * Complex.I * ((r * x 0 : ℝ) : ℂ)) *
      ((plusPow δ (1 - ∑ i, x i ^ 2) : ℝ) : ℂ) with hG
  set H : ℝ × (Fin k → ℝ) → ℂ := fun p =>
    Complex.exp (2 * Real.pi * Complex.I * ((r * p.1 : ℝ) : ℂ)) *
      ((plusPow δ ((1 - p.1 ^ 2) - ∑ i, p.2 i ^ 2) : ℝ) : ℂ) with hH
  have hC : Kfun (k + 1) δ (r • EuclideanSpace.single (0 : Fin (k + 1)) (1 : ℝ)) =
      ∫ x, G x := by
    rw [Kfun, Real.fourierInv_eq']
    rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (k + 1))).integral_comp' G]
    congr 1; funext v
    have hin : ⟪v, r • EuclideanSpace.single (0 : Fin (k + 1)) (1 : ℝ)⟫ = r * v 0 := by
      simp [inner_smul_right, EuclideanSpace.inner_single_right]
    have hn : ‖v‖ ^ 2 = ∑ i, v i ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]; simp [sq_abs]
    have hv : ∀ i, (MeasurableEquiv.toLp 2 (Fin (k + 1) → ℝ)).symm v i = v i := fun i => rfl
    simp only [hG, brSymbol, hin, hn, smul_eq_mul, hv]
    congr 2
    push_cast; ring
  have hD : ∫ x, G x = ∫ p, H p := by
    rw [← (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm.integral_comp' G]
    congr 1; funext p
    simp [hG, hH, MeasurableEquiv.piFinSuccAbove, Fin.sum_univ_succ]
    congr 1; ring
  have hHm : Measurable H := by
    have h1 : Measurable (fun p : ℝ × (Fin k → ℝ) => plusPow δ ((1 - p.1 ^ 2) - ∑ i, p.2 i ^ 2)) :=
      (plusPow_measurable δ).comp (by fun_prop)
    have h2 := Complex.measurable_ofReal.comp h1
    simp only [hH]
    fun_prop
  have hint : Integrable H (volume : Measure (ℝ × (Fin k → ℝ))) := by
    refine integrable_of_bdd H hHm.aestronglyMeasurable 1 ?_ (closedBall 0 1)
      measurableSet_closedBall measure_closedBall_lt_top ?_
    · intro p
      simp only [hH, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (plusPow_nonneg _ _)]
      have he : ‖Complex.exp (2 * Real.pi * Complex.I * ((r * p.1 : ℝ) : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [he, one_mul]
      exact plusPow_le_one _ _ hδ (by
        have : 0 ≤ ∑ i, p.2 i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
        nlinarith)
    · intro p hp
      have h1 : 0 < (1 - p.1 ^ 2) - ∑ i, p.2 i ^ 2 := by
        by_contra hc
        apply hp
        simp only [hH]
        rw [plusPow_eq_zero _ _ (not_lt.1 hc), Complex.ofReal_zero, mul_zero]
      have hs : 0 ≤ ∑ i, p.2 i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      rw [mem_closedBall, dist_zero_right, norm_prod_le_iff]
      constructor
      · rw [Real.norm_eq_abs, abs_le]; constructor <;> nlinarith
      · rw [pi_norm_le_iff_of_nonneg zero_le_one]
        intro i
        have : p.2 i ^ 2 ≤ ∑ j, p.2 j ^ 2 :=
          Finset.single_le_sum (f := fun j => p.2 j ^ 2) (fun j _ => sq_nonneg _)
            (Finset.mem_univ i)
        rw [Real.norm_eq_abs, abs_le]; constructor <;> nlinarith
  have hE : ∫ p, H p = ∫ t : ℝ, (c0 : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * ((r * t : ℝ) : ℂ)) *
      ((plusPow μ (1 - t ^ 2) : ℝ) : ℂ)) := by
    rw [Measure.volume_eq_prod, integral_prod H hint]
    congr 1; funext t
    simp only [hH]
    rw [integral_const_mul, integral_complex_ofReal, inner_integral]
    push_cast; ring
  have hI : ∫ t : ℝ, Complex.exp (2 * Real.pi * Complex.I * ((r * t : ℝ) : ℂ)) *
      ((plusPow μ (1 - t ^ 2) : ℝ) : ℂ) = I1 μ r := by
    rw [I1, intervalIntegral.integral_of_le (by norm_num),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioc (-1 : ℝ) 1)
        (μ := volume)]
    · apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      have h0 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
      simp only
      congr 2
      rcases h0.lt_or_eq with h | h
      · rw [plusPow, if_pos h]
      · rw [← h, plusPow, if_neg (lt_irrefl 0), Real.zero_rpow hμpos.ne']
    · intro t ht
      rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
      have : 1 - t ^ 2 ≤ 0 := by rcases ht with h | h <;> nlinarith
      rw [plusPow_eq_zero _ _ this, Complex.ofReal_zero, mul_zero]
  rw [hC, hD, hE, integral_const_mul, hI]

theorem Kfun_eq_radial (hn : 2 ≤ n) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ z : E n, Kfun n δ z = c * I1 (δ + ((n : ℝ) - 1) / 2) ‖z‖ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨∫ η : Fin k → ℝ, plusPow δ (1 - ∑ i, η i ^ 2), (c0_pos k δ hδ).ne', fun z => ?_⟩
  have hμ : δ + (((k + 1 : ℕ) : ℝ) - 1) / 2 = δ + (k : ℝ) / 2 := by push_cast; ring
  rw [hμ]
  have hnorm : ‖z‖ = ‖‖z‖ • EuclideanSpace.single (0 : Fin (k + 1)) (1 : ℝ)‖ := by
    simp [norm_smul]
  rw [← Kfun_isometry δ (Submodule.reflection (ℝ ∙ (z - ‖z‖ • EuclideanSpace.single (0 : Fin (k + 1))
    (1 : ℝ)))ᗮ) z, Submodule.reflection_sub hnorm, Kfun_axis k (by omega) δ ‖z‖ hδ]

end TaoBR.CS.PartK
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR
namespace CS
variable {n : ℕ}
/-! ## Part R: the kernel is a one-dimensional integral -/
alias Kfun_eq_radial := TaoBR.CS.PartK.Kfun_eq_radial

end CS
end TaoBR
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR.CS.PartC
open Filter Topology Set Asymptotics
open scoped Interval
/-! ## Exponential-decay bounds -/
lemma bound_isBigO {b a p T : ℝ} (hb : 0 < b) (hT : 0 ≤ T) (hp : 0 ≤ p) :
    (fun u : ℝ => Real.exp (-b * u) * u ^ a * (2 + T * u) ^ p) =O[atTop]
      (fun u => Real.exp (-(b / 2) * u)) := by
  have hlo := (isLittleO_rpow_exp_pos_mul_atTop (a + p) (half_pos hb)).bound zero_lt_one
  refine IsBigO.of_bound ((2 + T) ^ p) ?_
  filter_upwards [hlo, eventually_ge_atTop (1 : ℝ)] with u hu hu1
  have hu0 : 0 < u := by linarith
  rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hu
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have h1 : (2 + T * u) ^ p ≤ (2 + T) ^ p * u ^ p := by
    rw [← Real.mul_rpow (by positivity) hu0.le]
    apply Real.rpow_le_rpow (by positivity) _ hp
    nlinarith
  have h2 : Real.exp (-b * u) * Real.exp (b / 2 * u) = Real.exp (-(b / 2) * u) := by
    rw [← Real.exp_add]; ring_nf
  calc Real.exp (-b * u) * u ^ a * (2 + T * u) ^ p
      ≤ Real.exp (-b * u) * u ^ a * ((2 + T) ^ p * u ^ p) := by gcongr
    _ = (2 + T) ^ p * (Real.exp (-b * u) * u ^ (a + p)) := by rw [Real.rpow_add hu0]; ring
    _ ≤ (2 + T) ^ p * (Real.exp (-b * u) * Real.exp (b / 2 * u)) := by gcongr
    _ = _ := by rw [h2]

lemma bound_integrable {b a p T : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (hT : 0 ≤ T) (hp : 0 ≤ p) :
    IntegrableOn (fun u : ℝ => Real.exp (-b * u) * u ^ a * (2 + T * u) ^ p) (Ioi 0) := by
  refine integrable_of_isBigO_exp_neg (half_pos hb) ?_ (bound_isBigO hb hT hp)
  refine Continuous.continuousOn ?_
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (Real.continuous_rpow_const ha)).mul
    ((Real.continuous_rpow_const hp).comp (continuous_const.add (continuous_const.mul continuous_id)))

lemma bound_tendsto {b a p T : ℝ} (hb : 0 < b) (hT : 0 ≤ T) (hp : 0 ≤ p) :
    Tendsto (fun u : ℝ => Real.exp (-b * u) * u ^ a * (2 + T * u) ^ p) atTop (𝓝 0) := by
  refine (bound_isBigO hb hT hp).trans_tendsto ?_
  exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))

lemma rpow_le_rpow_abs {x M e : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ M) : x ^ e ≤ M ^ |e| := by
  rcases le_or_gt 0 e with he | he
  · rw [abs_of_nonneg he]; exact Real.rpow_le_rpow (by linarith) h2 he
  · calc x ^ e ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 he.le
      _ ≤ M ^ |e| := Real.one_le_rpow (by linarith) (abs_nonneg e)

/-! ## The amplitude and its derivatives -/
/-- weight -/
noncomputable def W (μ u : ℝ) : ℂ := -Complex.I * ((Real.exp (-2 * Real.pi * u) * u ^ μ : ℝ) : ℂ)

/-- derivative constants -/
noncomputable def cK (μ : ℝ) (k : ℕ) : ℂ := ∏ j ∈ Finset.range k, ((μ : ℂ) - j)

/-- k-th τ-derivative of the integrand of `Aμ`. -/
noncomputable def G (μ : ℝ) (k : ℕ) (τ u : ℝ) : ℂ :=
  W μ u * (cK μ k * (u : ℂ) ^ k * (((τ * u : ℝ) : ℂ) - 2 * Complex.I) ^ ((μ : ℂ) - k))

lemma Aμ_eq_G (μ τ : ℝ) : TaoBR.CS.Aμ μ τ = ∫ u in Ioi 0, G μ 0 τ u := by
  unfold TaoBR.CS.Aμ G W cK
  simp

lemma slit (τ u : ℝ) : (((τ * u : ℝ) : ℂ) - 2 * Complex.I) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right; simp

lemma G_continuous (μ : ℝ) (hμ : 0 ≤ μ) (k : ℕ) (τ : ℝ) : Continuous (G μ k τ) := by
  unfold G W
  refine (continuous_const.mul (Complex.continuous_ofReal.comp
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_rpow_const hμ)))).mul ?_
  refine (continuous_const.mul (Complex.continuous_ofReal.pow k)).mul ?_
  refine Continuous.cpow ?_ continuous_const (fun u => slit τ u)
  exact (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).sub continuous_const

lemma G_norm_le (μ : ℝ) (k : ℕ) (τ u T : ℝ) (hu : 0 < u) (hτ : |τ| ≤ T) :
    ‖G μ k τ u‖ ≤ ‖cK μ k‖ * (Real.exp (-(2 * Real.pi) * u) * u ^ (μ + k) *
      (2 + T * u) ^ |μ - k|) := by
  have hz1 : 1 ≤ ‖(((τ * u : ℝ) : ℂ) - 2 * Complex.I)‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simp
  have hz2 : ‖(((τ * u : ℝ) : ℂ) - 2 * Complex.I)‖ ≤ 2 + T * u := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hu]
    have : ‖(2 : ℂ) * Complex.I‖ = 2 := by simp
    rw [this]; nlinarith
  have hc : ((μ : ℂ) - k) = ((μ - k : ℝ) : ℂ) := by push_cast; ring
  unfold G W
  rw [hc, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_cpow_real, norm_neg,
    Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_pow,
    Complex.norm_real, Real.norm_of_nonneg hu.le, Real.rpow_add hu, Real.rpow_natCast]
  have := rpow_le_rpow_abs (e := μ - k) hz1 hz2
  have h0 : 0 ≤ ‖cK μ k‖ * u ^ k := by positivity
  calc 1 * (Real.exp (-2 * Real.pi * u) * u ^ μ) * (‖cK μ k‖ * u ^ k *
        ‖(((τ * u : ℝ) : ℂ) - 2 * Complex.I)‖ ^ (μ - k))
      ≤ 1 * (Real.exp (-2 * Real.pi * u) * u ^ μ) * (‖cK μ k‖ * u ^ k * (2 + T * u) ^ |μ - k|) := by
        gcongr
    _ = _ := by ring_nf

lemma G_integrable (μ : ℝ) (hμ : 0 ≤ μ) (k : ℕ) (τ : ℝ) :
    IntegrableOn (G μ k τ) (Ioi 0) := by
  have hb := (bound_integrable (b := 2 * Real.pi) (a := μ + k) (p := |μ - k|) (T := |τ|)
    (by positivity) (by positivity) (abs_nonneg _) (abs_nonneg _)).const_mul ‖cK μ k‖
  refine hb.mono' ((G_continuous μ hμ k τ).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
  exact G_norm_le μ k τ u |τ| hu le_rfl

lemma G_hasDerivAt (μ : ℝ) (k : ℕ) (τ u : ℝ) :
    HasDerivAt (fun τ => G μ k τ u) (G μ (k + 1) τ u) τ := by
  have hz : HasDerivAt (fun τ : ℝ => (((τ * u : ℝ) : ℂ) - 2 * Complex.I)) ((u : ℝ) : ℂ) τ := by
    have := ((hasDerivAt_id τ).mul_const u).ofReal_comp
    simpa using this.sub_const (2 * Complex.I)
  have hp := ((Complex.hasStrictDerivAt_cpow_const (c := (μ : ℂ) - k) (slit τ u)).hasDerivAt.comp
    τ hz).const_mul (cK μ k * (u : ℂ) ^ k) |>.const_mul (W μ u)
  unfold G
  refine hp.congr_deriv ?_
  simp only [cK, Finset.prod_range_succ]
  have : (μ : ℂ) - ((k + 1 : ℕ) : ℂ) = (μ : ℂ) - k - 1 := by push_cast; ring
  rw [this, pow_succ]
  ring

/-- the derivative family -/
noncomputable def F (μ : ℝ) (k : ℕ) (τ : ℝ) : ℂ := ∫ u in Ioi 0, G μ k τ u

lemma F_hasDerivAt (μ : ℝ) (hμ : 0 ≤ μ) (k : ℕ) (τ₀ : ℝ) :
    HasDerivAt (F μ k) (F μ (k + 1) τ₀) τ₀ := by
  set T := |τ₀| + 1
  have hb := (bound_integrable (b := 2 * Real.pi) (a := μ + ((k + 1 : ℕ) : ℝ))
    (p := |μ - ((k + 1 : ℕ) : ℝ)|) (T := T)
    (by positivity) (by positivity) (by positivity) (abs_nonneg _)).const_mul ‖cK μ (k + 1)‖
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun τ u => G μ k τ u) (F' := fun τ u => G μ (k + 1) τ u) (x₀ := τ₀)
    (ball_mem_nhds τ₀ one_pos)
    (Eventually.of_forall fun τ => (G_continuous μ hμ k τ).aestronglyMeasurable)
    (G_integrable μ hμ k τ₀) ((G_continuous μ hμ (k + 1) τ₀).aestronglyMeasurable) ?_ hb
    (Eventually.of_forall fun u τ _ => G_hasDerivAt μ k τ u)
  · exact this.2
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu τ hτ => ?_)
    refine G_norm_le μ (k + 1) τ u T hu ?_
    rw [mem_ball, Real.dist_eq] at hτ
    have := abs_sub_abs_le_abs_sub τ τ₀
    simp only [T]; linarith

lemma F_contDiff (μ : ℝ) (hμ : 0 ≤ μ) (n : ℕ) : ∀ k, ContDiff ℝ n (F μ k) := by
  induction n with
  | zero =>
    intro k
    exact contDiff_zero.mpr
      (continuous_iff_continuousAt.mpr fun τ => (F_hasDerivAt μ hμ k τ).continuousAt)
  | succ n ih =>
    intro k
    have hd : deriv (F μ k) = F μ (k + 1) := funext fun τ => (F_hasDerivAt μ hμ k τ).deriv
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun τ => (F_hasDerivAt μ hμ k τ).differentiableAt, by simp, ?_⟩
    rw [hd]; exact ih (k + 1)

theorem Aμ_contDiff (μ : ℝ) (hμ : 0 < μ) : ContDiff ℝ (⊤ : ℕ∞) (Aμ μ) := by
  have : Aμ μ = F μ 0 := funext fun τ => Aμ_eq_G μ τ
  rw [this]
  exact contDiff_infty.mpr fun n => F_contDiff μ hμ.le n 0

end TaoBR.CS.PartC
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR
namespace CS
variable {n : ℕ}
/-! ## Part A: the amplitude -/
alias Aμ_contDiff := TaoBR.CS.PartC.Aμ_contDiff

end CS
end TaoBR
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR.CS.PartC
open Filter Topology Set Asymptotics
open scoped Interval
theorem Aμ_zero_ne (μ : ℝ) (hμ : 0 < μ) : Aμ μ 0 ≠ 0 := by
  have h : Aμ μ 0 = (-Complex.I * (-2 * Complex.I) ^ (μ : ℂ)) *
      ((∫ u in Ioi (0 : ℝ), u ^ ((μ + 1) - 1) * Real.exp (-((2 * Real.pi) * u)) : ℝ) : ℂ) := by
    unfold TaoBR.CS.Aμ
    rw [← integral_complex_ofReal, ← integral_const_mul]
    congr 1; funext u
    simp only [zero_mul, Complex.ofReal_zero, zero_sub, add_sub_cancel_right]
    push_cast; ring_nf
  rw [h, Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) (by positivity)]
  refine mul_ne_zero (mul_ne_zero (by simp) ?_) ?_
  · rw [Ne, Complex.cpow_eq_zero_iff]; simp
  · rw [Complex.ofReal_ne_zero]
    exact mul_ne_zero (by positivity) (Real.Gamma_pos_of_pos (by linarith)).ne'

/-! ## Contour deformation -/
/-- the holomorphic integrand -/
noncomputable def fC (μ r : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z) * (1 - z ^ 2) ^ (μ : ℂ)

lemma re_one_sub_sq (z : ℂ) : (1 - z ^ 2).re = 1 - z.re ^ 2 + z.im ^ 2 := by
  simp [sq, Complex.mul_re]; ring

lemma fC_rect (μ r : ℝ) (hμ : 0 < μ) (H : ℝ) :
    (∫ x : ℝ in (-1)..1, fC μ r x) - (∫ x : ℝ in (-1)..1, fC μ r (x + H * Complex.I)) +
      Complex.I • (∫ y : ℝ in (0 : ℝ)..H, fC μ r (1 + y * Complex.I)) -
      Complex.I • (∫ y : ℝ in (0 : ℝ)..H, fC μ r (-1 + y * Complex.I)) = 0 := by
  have hc : ContinuousOn (fC μ r)
      ([[(-1 : ℂ).re, (1 + H * Complex.I).re]] ×ℂ [[(-1 : ℂ).im, (1 + H * Complex.I).im]]) := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    obtain ⟨h1, -⟩ := hz
    simp only [Complex.neg_re, Complex.one_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
      Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), Set.mem_Icc] at h1
    have hre : 0 ≤ (1 - z ^ 2).re := by
      rw [re_one_sub_sq]; nlinarith [sq_nonneg z.im]
    apply ContinuousAt.continuousWithinAt
    unfold fC
    refine ((continuous_const.mul continuous_id).cexp.continuousAt).mul ?_
    exact ContinuousAt.comp (g := fun w : ℂ => w ^ (μ : ℂ))
      (Complex.continuousAt_cpow_const_of_re_pos (Or.inl hre) (by simpa using hμ))
      ((continuous_const.sub (continuous_pow 2)).continuousAt)
  have hd : DifferentiableOn ℂ (fC μ r)
      (Ioo (min (-1 : ℂ).re (1 + H * Complex.I).re) (max (-1 : ℂ).re (1 + H * Complex.I).re) ×ℂ
        Ioo (min (-1 : ℂ).im (1 + H * Complex.I).im) (max (-1 : ℂ).im (1 + H * Complex.I).im)) := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    obtain ⟨h1, -⟩ := hz
    simp only [Complex.neg_re, Complex.one_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
      Set.mem_Ioo] at h1
    norm_num at h1
    have hre : 0 < (1 - z ^ 2).re := by
      rw [re_one_sub_sq]; nlinarith [sq_nonneg z.im]
    apply DifferentiableAt.differentiableWithinAt
    unfold fC
    refine ((differentiableAt_id.const_mul _).cexp).mul ?_
    exact ((differentiableAt_const _).sub (differentiableAt_pow 2)).cpow (differentiableAt_const _)
      (Or.inl hre)
  have := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn (fC μ r)
    (-1) (1 + H * Complex.I) hc hd
  simpa using this

lemma fC_bottom (μ r : ℝ) : ∫ x : ℝ in (-1)..1, fC μ r x = TaoBR.CS.I1 μ r := by
  unfold TaoBR.CS.I1
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le (by norm_num)] at hx
  have h0 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  simp only [fC]
  rw [Complex.ofReal_cpow h0]; push_cast; ring_nf

lemma fC_top_norm (μ r H : ℝ) (hμ : 0 < μ) (hH : 0 ≤ H) (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖fC μ r (x + H * Complex.I)‖ ≤
      Real.exp (-(2 * Real.pi * r) * H) * H ^ (0 : ℝ) * (2 + 1 * H) ^ (2 * μ) := by
  unfold fC
  rw [norm_mul, Complex.norm_exp, Complex.norm_cpow_real, Real.rpow_zero, mul_one, one_mul]
  have hre : (2 * Real.pi * Complex.I * (r : ℂ) * (x + H * Complex.I)).re = -(2 * Real.pi * r) * H := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  gcongr
  have hn : ‖(1 : ℂ) - (x + H * Complex.I) ^ 2‖ ≤ (2 + H) ^ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_pow, Complex.sq_norm, Complex.normSq_add_mul_I]
    nlinarith [hx.1, hx.2]
  rw [Real.rpow_mul (by positivity), Real.rpow_two]
  exact Real.rpow_le_rpow (norm_nonneg _) hn hμ.le

lemma top_tendsto (μ r : ℝ) (hμ : 0 < μ) (hr : 0 < r) :
    Tendsto (fun H : ℝ => ∫ x : ℝ in (-1)..1, fC μ r (x + H * Complex.I)) atTop (𝓝 0) := by
  have ht := (bound_tendsto (b := 2 * Real.pi * r) (a := 0) (T := 1) (p := 2 * μ)
    (by positivity) zero_le_one (by positivity)).mul_const |(1 : ℝ) - (-1)|
  rw [zero_mul] at ht
  refine squeeze_zero_norm' ?_ ht
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  rw [Set.uIoc_of_le (by norm_num)] at hx
  exact fC_top_norm μ r H hμ hH x (Set.Ioc_subset_Icc_self hx)

lemma ofReal_mul_cpow {y : ℝ} (hy : 0 < y) {w : ℂ} (hw : w ≠ 0) (s : ℂ) :
    ((y : ℂ) * w) ^ s = (y : ℂ) ^ s * w ^ s := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hy' hw), Complex.cpow_def_of_ne_zero hy',
    Complex.cpow_def_of_ne_zero hw, Complex.log_ofReal_mul hy hw, ← Complex.exp_add,
    Complex.ofReal_log hy.le]
  ring_nf

lemma G0_eq (μ r : ℝ) (hr : 0 < r) (y : ℝ) (hy : 0 < y) :
    G μ 0 r⁻¹ (r * y) = -Complex.I * ((Real.exp (-2 * Real.pi * (r * y)) : ℝ) : ℂ) *
      (((r ^ μ : ℝ) : ℂ) * ((y ^ μ : ℝ) : ℂ)) * ((y : ℂ) - 2 * Complex.I) ^ (μ : ℂ) := by
  unfold G W cK
  have : r⁻¹ * (r * y) = y := by field_simp
  rw [this, Real.mul_rpow hr.le hy.le]
  push_cast
  ring_nf

lemma fC_right (μ r : ℝ) (hr : 0 < r) (y : ℝ) (hy : 0 < y) :
    fC μ r (1 + y * Complex.I) = Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) *
      ((r ^ (-μ) : ℝ) : ℂ) * Complex.I * G μ 0 r⁻¹ (r * y) := by
  have hw : ((y : ℂ) - 2 * Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have e1 : (1 - (1 + (y : ℂ) * Complex.I) ^ 2) = (y : ℂ) * ((y : ℂ) - 2 * Complex.I) := by
    linear_combination (-(y : ℂ) ^ 2) * Complex.I_sq
  have e2 : Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (1 + y * Complex.I)) =
      Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) *
        ((Real.exp (-2 * Real.pi * (r * y)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast
    linear_combination (2 * Real.pi * r * y : ℂ) * Complex.I_sq
  have e5 : ((r ^ (-μ) : ℝ) : ℂ) * ((r ^ μ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, Real.rpow_neg hr.le, inv_mul_cancel₀ (by positivity),
      Complex.ofReal_one]
  unfold fC
  rw [e1, ofReal_mul_cpow hy hw, ← Complex.ofReal_cpow hy.le, e2, G0_eq μ r hr y hy]
  set E := Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))
  set X := ((Real.exp (-2 * Real.pi * (r * y)) : ℝ) : ℂ)
  set Y := ((y ^ μ : ℝ) : ℂ)
  set P := ((y : ℂ) - 2 * Complex.I) ^ (μ : ℂ)
  set R := ((r ^ (-μ) : ℝ) : ℂ)
  set M := ((r ^ μ : ℝ) : ℂ)
  linear_combination (-(E * X * Y * P)) * e5 + (E * X * Y * P * R * M) * Complex.I_sq

lemma conj_P (y μ : ℝ) :
    (starRingEnd ℂ) (((y : ℂ) - 2 * Complex.I) ^ (μ : ℂ)) = ((y : ℂ) + 2 * Complex.I) ^ (μ : ℂ) := by
  have harg : ((y : ℂ) + 2 * Complex.I).arg ≠ Real.pi := by
    rw [Ne, Complex.arg_eq_pi_iff]; simp
  have := Complex.cpow_conj ((y : ℂ) + 2 * Complex.I) (μ : ℂ) harg
  rw [Complex.conj_ofReal] at this
  rw [this]
  congr 2
  apply Complex.ext <;> simp

lemma fC_left (μ r : ℝ) (hr : 0 < r) (y : ℝ) (hy : 0 < y) :
    fC μ r (-1 + y * Complex.I) = Complex.exp (-(2 * Real.pi * Complex.I * (r : ℂ))) *
      ((r ^ (-μ) : ℝ) : ℂ) * (-Complex.I) * (starRingEnd ℂ) (G μ 0 r⁻¹ (r * y)) := by
  have hw : ((y : ℂ) + 2 * Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have e1 : (1 - (-1 + (y : ℂ) * Complex.I) ^ 2) = (y : ℂ) * ((y : ℂ) + 2 * Complex.I) := by
    linear_combination (-(y : ℂ) ^ 2) * Complex.I_sq
  have e2 : Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (-1 + y * Complex.I)) =
      Complex.exp (-(2 * Real.pi * Complex.I * (r : ℂ))) *
        ((Real.exp (-2 * Real.pi * (r * y)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast
    linear_combination (2 * Real.pi * r * y : ℂ) * Complex.I_sq
  have e5 : ((r ^ (-μ) : ℝ) : ℂ) * ((r ^ μ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, Real.rpow_neg hr.le, inv_mul_cancel₀ (by positivity),
      Complex.ofReal_one]
  have e3 : (starRingEnd ℂ) (G μ 0 r⁻¹ (r * y)) = Complex.I *
      ((Real.exp (-2 * Real.pi * (r * y)) : ℝ) : ℂ) * (((r ^ μ : ℝ) : ℂ) * ((y ^ μ : ℝ) : ℂ)) *
        ((y : ℂ) + 2 * Complex.I) ^ (μ : ℂ) := by
    rw [G0_eq μ r hr y hy]
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, conj_P, neg_neg]
  unfold fC
  rw [e1, ofReal_mul_cpow hy hw, ← Complex.ofReal_cpow hy.le, e2, e3]
  set E := Complex.exp (-(2 * Real.pi * Complex.I * (r : ℂ)))
  set X := ((Real.exp (-2 * Real.pi * (r * y)) : ℝ) : ℂ)
  set Y := ((y ^ μ : ℝ) : ℂ)
  set P := ((y : ℂ) + 2 * Complex.I) ^ (μ : ℂ)
  set R := ((r ^ (-μ) : ℝ) : ℂ)
  set M := ((r ^ μ : ℝ) : ℂ)
  linear_combination (-(E * X * Y * P)) * e5 + (E * X * Y * P * R * M) * Complex.I_sq

theorem I1_eq (μ : ℝ) (hμ : 0 < μ) (r : ℝ) (hr : 0 < r) :
    I1 μ r = ((r ^ (-μ - 1) : ℝ) : ℂ) *
      (Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) * Aμ μ r⁻¹ +
        Complex.exp (-(2 * Real.pi * Complex.I * (r : ℂ))) * (starRingEnd ℂ) (Aμ μ r⁻¹)) := by
  set E := Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))
  set E' := Complex.exp (-(2 * Real.pi * Complex.I * (r : ℂ)))
  set R := ((r ^ (-μ) : ℝ) : ℂ)
  have hGi : IntegrableOn (fun y => G μ 0 r⁻¹ (r * y)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff (G μ 0 r⁻¹) 0 hr).mpr
      (by rw [mul_zero]; exact G_integrable μ hμ.le 0 r⁻¹)
  have hRi : IntegrableOn (fun y : ℝ => fC μ r (1 + y * Complex.I)) (Ioi 0) :=
    IntegrableOn.congr_fun (hGi.const_mul (E * R * Complex.I))
      (fun y hy => (fC_right μ r hr y hy).symm) measurableSet_Ioi
  have hLi : IntegrableOn (fun y : ℝ => fC μ r (-1 + y * Complex.I)) (Ioi 0) := by
    have : IntegrableOn (fun y : ℝ => E' * R * (-Complex.I) *
        (Complex.conjCLE : ℂ →L[ℝ] ℂ) (G μ 0 r⁻¹ (r * y))) (Ioi 0) :=
      (ContinuousLinearMap.integrable_comp (Complex.conjCLE : ℂ →L[ℝ] ℂ) hGi).const_mul
        (E' * R * (-Complex.I))
    refine IntegrableOn.congr_fun this (fun y hy => ?_) measurableSet_Ioi
    simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply]
    exact (fC_left μ r hr y hy).symm
  have hRv : ∫ y : ℝ in Ioi 0, fC μ r (1 + (y : ℂ) * Complex.I) =
      E * R * Complex.I * (((r⁻¹ : ℝ) : ℂ) * Aμ μ r⁻¹) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => fC_right μ r hr y hy),
      integral_const_mul, integral_comp_mul_left_Ioi _ _ hr, mul_zero, ← Aμ_eq_G,
      Complex.real_smul]
  have hLv : ∫ y : ℝ in Ioi 0, fC μ r (-1 + (y : ℂ) * Complex.I) =
      E' * R * (-Complex.I) * (((r⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) (Aμ μ r⁻¹)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => fC_left μ r hr y hy),
      integral_const_mul, integral_conj, integral_comp_mul_left_Ioi _ _ hr, mul_zero, ← Aμ_eq_G,
      Complex.real_smul, map_mul, Complex.conj_ofReal]
  have hlim := ((top_tendsto μ r hμ hr).sub
    ((intervalIntegral_tendsto_integral_Ioi 0 hRi tendsto_id).const_mul Complex.I)).add
    ((intervalIntegral_tendsto_integral_Ioi 0 hLi tendsto_id).const_mul Complex.I)
  have heq : (fun _ : ℝ => I1 μ r) =ᶠ[atTop] (fun H : ℝ =>
      (∫ x : ℝ in (-1)..1, fC μ r (x + H * Complex.I)) -
        Complex.I * (∫ y : ℝ in (0 : ℝ)..id H, fC μ r (1 + y * Complex.I)) +
        Complex.I * (∫ y : ℝ in (0 : ℝ)..id H, fC μ r (-1 + y * Complex.I))) := by
    refine Eventually.of_forall fun H => ?_
    have := fC_rect μ r hμ H
    rw [fC_bottom] at this
    simp only [smul_eq_mul, id] at this ⊢
    linear_combination this
  have := tendsto_nhds_unique (tendsto_const_nhds.congr' heq) hlim
  rw [this, hRv, hLv]
  have hrp : ((r ^ (-μ - 1) : ℝ) : ℂ) = R * ((r⁻¹ : ℝ) : ℂ) := by
    rw [Real.rpow_sub hr, Real.rpow_one, div_eq_mul_inv, Complex.ofReal_mul]
  rw [hrp]
  linear_combination (-(E * R * ((r⁻¹ : ℝ) : ℂ) * Aμ μ r⁻¹ +
    E' * R * ((r⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) (Aμ μ r⁻¹))) * Complex.I_sq

end TaoBR.CS.PartC
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR
namespace CS
variable {n : ℕ}
/-! ## Part C: contour deformation -/
alias I1_eq := TaoBR.CS.PartC.I1_eq

alias Aμ_zero_ne := TaoBR.CS.PartC.Aμ_zero_ne

end CS
end TaoBR
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace Manifold
namespace TaoBR.CS.PartM
variable {n : ℕ}
lemma bounded_support_of_hasCompactSupport (ψ : E n → E n → ℝ)
    (hψc : HasCompactSupport (Function.uncurry ψ)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, ψ x y ≠ 0 → ‖x‖ ≤ L ∧ ‖y‖ ≤ L := by
  obtain ⟨L, hL⟩ := hψc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max L 0, le_max_right _ _, fun x y h => ?_⟩
  have hm : (x, y) ∈ tsupport (Function.uncurry ψ) := subset_tsupport _ (by simpa using h)
  have := hL hm
  rw [mem_closedBall, dist_zero_right, Prod.norm_def] at this
  exact ⟨(le_max_left _ _).trans (this.trans (le_max_left _ _)),
    (le_max_right _ _).trans (this.trans (le_max_left _ _))⟩

lemma norm_exp_two_pi_I' (t : ℝ) : ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))‖ = 1 := by
  rw [show 2 * Real.pi * Complex.I * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

theorem trivial_bound (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤) (ψ : E n → E n → ℝ)
    (hψ : Continuous (Function.uncurry ψ)) (hψc : HasCompactSupport (Function.uncurry ψ)) :
    ∃ C : ℝ≥0, ∀ R : ℝ, ∀ f : 𝓢(E n, ℂ),
      eLpNorm (carlesonSjolinOp ψ R f) p volume ≤ C * eLpNorm f p volume := by
  obtain ⟨L, -, hL⟩ := bounded_support_of_hasCompactSupport ψ hψc
  obtain ⟨M, hM⟩ := hψ.bounded_above_of_compact_support hψc
  set D : ℝ≥0∞ := ENNReal.ofReal M * volume (closedBall (0 : E n) L) ^ (1 - 1 / p.toReal) *
        volume (closedBall (0 : E n) L) ^ (1 / p.toReal)
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (by positivity) hpt
  have hp1 : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hpt hp; simpa using this
  have hDt : D ≠ ⊤ := by
    have hv : volume (closedBall (0 : E n) L) ≠ ⊤ := measure_closedBall_lt_top.ne
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) ?_
    · exact ENNReal.rpow_ne_top_of_nonneg (by rw [sub_nonneg, div_le_one hp0]; exact hp1) hv
    · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hv
  refine ⟨D.toNNReal, fun R f => ?_⟩
  rw [ENNReal.coe_toNNReal hDt]
  have hk : Continuous (Function.uncurry fun x y : E n =>
      Complex.exp (2 * Real.pi * Complex.I * ((R * ‖x - y‖ : ℝ) : ℂ)) * ((ψ x y : ℝ) : ℂ)) := by
    have h1 : Continuous (fun z : E n × E n => ψ z.1 z.2) := hψ
    fun_prop
  exact kernelOp_bound p hp hpt _ hk M L
    (fun x y => by
      rw [norm_mul, norm_exp_two_pi_I', one_mul, Complex.norm_real]
      exact hM (x, y))
    (fun x y h => hL x y (by intro h0; apply h; simp [h0]))
    f (f.memLp p volume)

end TaoBR.CS.PartM
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR
namespace CS
variable {n : ℕ}
/-! ## Part T: the trivial bound -/
alias trivial_bound := TaoBR.CS.PartM.trivial_bound

end CS
end TaoBR
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR.CS.PartP
variable {n : ℕ}
/-! ## Smooth clamps -/
lemma exists_clamp (a b ε : ℝ) (hab : a < b) (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ s, a ≤ s → s ≤ b → g s = s) ∧
      ∀ s, a - ε ≤ g s ∧ g s ≤ b + ε := by
  set m := (a + b) / 2
  let φ : ContDiffBump m := ⟨(b - a) / 2, (b - a) / 2 + ε, by linarith, by linarith⟩
  refine ⟨fun s => m + (s - m) * φ s, ?_, ?_, ?_⟩
  · exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul φ.contDiff)
  · intro s h1 h2
    have : φ s = 1 := φ.one_of_mem_closedBall (by
      rw [mem_closedBall, Real.dist_eq, abs_le]; constructor <;> simp only [m, φ] <;> linarith)
    simp [this]
  · intro s
    by_cases h : φ s = 0
    · simp only [h, mul_zero, add_zero, m]; constructor <;> linarith
    · have hs : s ∈ ball m ((b - a) / 2 + ε) := by
        by_contra hs
        exact h (φ.zero_of_le_dist (by simpa [mem_ball, dist_comm] using hs))
      rw [mem_ball, Real.dist_eq, abs_lt] at hs
      have h0 := φ.nonneg (x := s); have h1 := φ.le_one (x := s)
      dsimp only
      have hm : m = (a + b) / 2 := rfl
      rcases le_or_gt s m with hsm | hsm
      · have := mul_nonneg (sub_nonneg.2 hsm) (sub_nonneg.2 h1)
        have := mul_nonneg (sub_nonneg.2 hsm) h0
        constructor <;> nlinarith
      · have := mul_nonneg (sub_nonneg.2 hsm.le) (sub_nonneg.2 h1)
        have := mul_nonneg (sub_nonneg.2 hsm.le) h0
        constructor <;> nlinarith

/-! ## The amplitude functions -/
/-- `e(t) = e^{2πit}`. -/
noncomputable def ex (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))

lemma norm_ex (t : ℝ) : ‖ex t‖ = 1 := by
  rw [ex, show 2 * Real.pi * Complex.I * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

lemma ex_add (s t : ℝ) : ex (s + t) = ex s * ex t := by
  rw [ex, ex, ex, ← Complex.exp_add]; congr 1; push_cast; ring

lemma conj_ex (t : ℝ) : starRingEnd ℂ (ex t) = ex (-t) := by
  rw [ex, ex, ← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; push_cast; ring

lemma ex_contDiff : ContDiff ℝ (⊤ : ℕ∞) ex := by
  unfold ex
  exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

/-- `P_h(ρ, τ) = c ρ^{-μ-1} (1 + hτ)^ν A(τ / ((1 + hτ) ρ))`. -/
noncomputable def Pf (μ ν c h ρ τ : ℝ) : ℂ :=
  ((c * ρ ^ (-μ - 1) * (1 + h * τ) ^ ν : ℝ) : ℂ) * Aμ μ (τ / ((1 + h * τ) * ρ))

/-- The determinant `D = P₀ conj(e_h P_h) - conj(P₀) e_h P_h`. -/
noncomputable def Df (μ ν c h ρ τ : ℝ) : ℂ :=
  Pf μ ν c 0 ρ τ * starRingEnd ℂ (ex (h * ρ) * Pf μ ν c h ρ τ) -
    starRingEnd ℂ (Pf μ ν c 0 ρ τ) * (ex (h * ρ) * Pf μ ν c h ρ τ)

/-- The kernel formula: the normalized dilated Bochner–Riesz kernel at scale `R + h` is
`Z + conj Z` with `Z = e(Rρ) e(hρ) P_h(ρ, 1/R)`. -/
lemma kernel_formula (δ μ c : ℝ) (hμ : μ = δ + ((n : ℝ) - 1) / 2) (hμ0 : 0 < μ)
    (hc : ∀ z : E n, Kfun n δ z = c * I1 μ ‖z‖) (R h : ℝ) (hR : 0 < R) (hh : 0 ≤ h)
    (z : E n) (hz : 0 < ‖z‖) :
    ((R ^ (μ + 1 - n) * (R + h) ^ n : ℝ) : ℂ) * Kfun n δ ((R + h) • z) =
      ex (R * ‖z‖) * ex (h * ‖z‖) * Pf μ (n - μ - 1) c h ‖z‖ R⁻¹ +
        starRingEnd ℂ (ex (R * ‖z‖) * ex (h * ‖z‖) * Pf μ (n - μ - 1) c h ‖z‖ R⁻¹) := by
  set ρ := ‖z‖
  have hR' : 0 < R + h := by linarith
  have hnorm : ‖(R + h) • z‖ = (R + h) * ρ := by
    rw [norm_smul, Real.norm_of_nonneg hR'.le]
  rw [hc, hnorm, I1_eq μ hμ0 _ (by positivity)]
  have hτ : (R⁻¹ / ((1 + h * R⁻¹) * ρ)) = ((R + h) * ρ)⁻¹ := by
    field_simp
  have harg : (1 + h * R⁻¹) = (R + h) / R := by field_simp
  simp only [Pf, hτ, map_mul, Complex.conj_ofReal, conj_ex]
  have he1 : Complex.exp (2 * Real.pi * Complex.I * (((R + h) * ρ : ℝ) : ℂ)) =
      ex (R * ρ) * ex (h * ρ) := by rw [← ex_add, ex]; congr 3; ring
  have he2 : Complex.exp (-(2 * Real.pi * Complex.I * (((R + h) * ρ : ℝ) : ℂ))) =
      ex (-(R * ρ)) * ex (-(h * ρ)) := by
    rw [← ex_add, ex]; congr 1; push_cast; ring
  rw [he1, he2]
  have hρ : 0 < ρ := hz
  have key : ((R ^ (μ + 1 - n) * (R + h) ^ n : ℝ) : ℂ) * ((c : ℂ) * (((R + h) * ρ) ^ (-μ - 1) : ℝ)) =
      ((c * ρ ^ (-μ - 1) * (1 + h * R⁻¹) ^ ((n : ℝ) - μ - 1) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    have e1 : (R + h) ^ n * ((R + h) * ρ) ^ (-μ - 1) = (R + h) ^ ((n : ℝ) - μ - 1) * ρ ^ (-μ - 1) := by
      rw [Real.mul_rpow hR'.le hρ.le, ← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hR']
      ring_nf
    have e2 : (1 + h * R⁻¹) ^ ((n : ℝ) - μ - 1) = (R + h) ^ ((n : ℝ) - μ - 1) / R ^ ((n : ℝ) - μ - 1) := by
      rw [harg, Real.div_rpow hR'.le hR.le]
    have e3 : R ^ (μ + 1 - n) = (R ^ ((n : ℝ) - μ - 1))⁻¹ := by
      rw [← Real.rpow_neg hR.le]; ring_nf
    have hpos : 0 < R ^ ((n : ℝ) - μ - 1) := Real.rpow_pos_of_pos hR _
    calc R ^ (μ + 1 - n) * (R + h) ^ n * (c * ((R + h) * ρ) ^ (-μ - 1))
        = c * R ^ (μ + 1 - n) * ((R + h) ^ n * ((R + h) * ρ) ^ (-μ - 1)) := by ring
      _ = _ := by rw [e1, e2, e3]; field_simp
  linear_combination (ex (R * ρ) * ex (h * ρ) * Aμ μ ((R + h) * ρ)⁻¹ +
    ex (-(R * ρ)) * ex (-(h * ρ)) * starRingEnd ℂ (Aμ μ ((R + h) * ρ)⁻¹)) * key

/-! ## Smoothness of `P` and `D`, and `D ≠ 0` near `τ = 0` -/
/-- The open domain `ρ > 0`, `1 + hτ > 0`. -/
def Ω (h : ℝ) : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ 0 < 1 + h * q.2}

lemma isOpen_Ω (h : ℝ) : IsOpen (Ω h) :=
  (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_const (continuous_const.add (continuous_const.mul continuous_snd)))

lemma Pf_contDiffOn (μ ν c h : ℝ) (hμ0 : 0 < μ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => Pf μ ν c h q.1 q.2) (Ω h) := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => q.1 ^ (-μ - 1)) q :=
    contDiffAt_fst.rpow_const_of_ne hq.1.ne'
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => (1 + h * q.2) ^ ν) q :=
    (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_snd)).rpow_const_of_ne hq.2.ne'
  have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => q.2 / ((1 + h * q.2) * q.1)) q :=
    contDiffAt_snd.div ((contDiffAt_const.add (contDiffAt_const.mul contDiffAt_snd)).mul
      contDiffAt_fst) (mul_pos hq.2 hq.1).ne'
  have h4 : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => Aμ μ (q.2 / ((1 + h * q.2) * q.1))) q :=
    (Aμ_contDiff μ hμ0).contDiffAt.comp q h3
  have h5 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => ((c * q.1 ^ (-μ - 1) * (1 + h * q.2) ^ ν : ℝ) : ℂ)) q :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp q ((contDiffAt_const.mul h1).mul h2)
  exact h5.mul h4

lemma conj_contDiff : ContDiff ℝ (⊤ : ℕ∞) (starRingEnd ℂ) :=
  Complex.conjCLE.contDiff

lemma Df_contDiffOn (μ ν c h : ℝ) (hμ0 : 0 < μ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => Df μ ν c h q.1 q.2) (Ω h) := by
  have hΩ0 : Ω h ⊆ Ω 0 := fun q hq => ⟨hq.1, by simp⟩
  have hP0 := (Pf_contDiffOn μ ν c 0 hμ0).mono hΩ0
  have hPh := Pf_contDiffOn μ ν c h hμ0
  have he : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => ex (h * q.1)) (Ω h) :=
    (ex_contDiff.comp (contDiff_const.mul contDiff_fst)).contDiffOn
  have hePh := he.mul hPh
  unfold Df
  exact (hP0.mul (conj_contDiff.comp_contDiffOn hePh)).sub
    ((conj_contDiff.comp_contDiffOn hP0).mul hePh)

lemma Df_zero (μ ν c h ρ : ℝ) :
    Df μ ν c h ρ 0 = ((Complex.normSq (Pf μ ν c 0 ρ 0) : ℝ) : ℂ) *
      (starRingEnd ℂ (ex (h * ρ)) - ex (h * ρ)) := by
  have : Pf μ ν c h ρ 0 = Pf μ ν c 0 ρ 0 := by simp [Pf]
  rw [Df, this, Complex.normSq_eq_conj_mul_self, map_mul]
  push_cast; ring

lemma Df_zero_ne (μ ν c h ρ : ℝ) (hμ0 : 0 < μ) (hc : c ≠ 0) (hρ : 0 < ρ) (hh : 0 < h)
    (hhρ : h * ρ < 1 / 2) : Df μ ν c h ρ 0 ≠ 0 := by
  rw [Df_zero]
  refine mul_ne_zero ?_ ?_
  · have hP : Pf μ ν c 0 ρ 0 ≠ 0 := by
      simp only [Pf, zero_mul, add_zero, Real.one_rpow, mul_one, zero_div]
      exact mul_ne_zero (by exact_mod_cast mul_ne_zero hc (Real.rpow_pos_of_pos hρ _).ne')
        (Aμ_zero_ne μ hμ0)
    exact_mod_cast (Complex.normSq_pos.2 hP).ne'
  · intro h0
    have him := congrArg Complex.im h0
    rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at him
    have : (ex (h * ρ)).im = Real.sin (2 * Real.pi * (h * ρ)) := by
      rw [ex, show 2 * Real.pi * Complex.I * ((h * ρ : ℝ) : ℂ) =
        ((2 * Real.pi * (h * ρ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_ofReal_mul_I_im]
    have hs : 0 < Real.sin (2 * Real.pi * (h * ρ)) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · have := Real.pi_pos; positivity
      · have := Real.pi_pos; nlinarith
    linarith

lemma D_ne (μ ν c h ρa ρb : ℝ) (hμ0 : 0 < μ) (hc : c ≠ 0) (hρa : 0 < ρa) (hh : 0 < h)
    (hhρ : h * ρb < 1 / 2) :
    ∃ τ₁ : ℝ, 0 < τ₁ ∧ h * τ₁ ≤ 1 / 2 ∧
      ∀ ρ ∈ Set.Icc ρa ρb, ∀ τ, |τ| ≤ τ₁ → (ρ, τ) ∈ Ω h ∧ Df μ ν c h ρ τ ≠ 0 := by
  set U := Ω h ∩ (fun q : ℝ × ℝ => Df μ ν c h q.1 q.2) ⁻¹' {0}ᶜ
  have hU : IsOpen U := (Df_contDiffOn μ ν c h hμ0).continuousOn.isOpen_inter_preimage
    (isOpen_Ω h) isOpen_compl_singleton
  have hK : IsCompact (Set.Icc ρa ρb ×ˢ ({0} : Set ℝ)) := isCompact_Icc.prod isCompact_singleton
  have hKU : Set.Icc ρa ρb ×ˢ ({0} : Set ℝ) ⊆ U := by
    rintro ⟨ρ, τ⟩ ⟨hρ, hτ⟩
    simp only [Set.mem_singleton_iff] at hτ; subst hτ
    refine ⟨⟨by simp; linarith [hρ.1], by simp⟩, ?_⟩
    exact Df_zero_ne μ ν c h ρ hμ0 hc (by linarith [hρ.1]) hh
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hρ.2 hh.le) hhρ)
  obtain ⟨ε, hε, hεU⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨min (ε / 2) (1 / (2 * h)), by positivity, ?_, ?_⟩
  · calc h * min (ε / 2) (1 / (2 * h)) ≤ h * (1 / (2 * h)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hh.le
      _ = 1 / 2 := by field_simp
  · intro ρ hρ τ hτ
    have hmem : (ρ, τ) ∈ Metric.thickening ε (Set.Icc ρa ρb ×ˢ ({0} : Set ℝ)) := by
      rw [Metric.mem_thickening_iff]
      refine ⟨(ρ, 0), ⟨hρ, rfl⟩, ?_⟩
      rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, max_eq_right (abs_nonneg τ)]
      linarith [min_le_left (ε / 2) (1 / (2 * h))]
    exact hεU hmem

/-! ## Uniform derivative bounds for a jointly smooth amplitude -/
lemma der_bound (Φ : (E n × ℝ) × E n → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (Λ : ℝ) (k : ℕ) :
    ∃ D : ℝ, ∀ y : E n, ‖y‖ ≤ Λ → ∀ z : E n × ℝ, ‖z‖ < Λ →
      ‖iteratedFDeriv ℝ k (fun z : E n × ℝ => Φ (z, y)) z‖ ≤ D := by
  have hcont : Continuous (fun w => iteratedFDeriv ℝ k Φ w) :=
    hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : (E n × ℝ) × E n) Λ).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨D, fun y hy z hz => ?_⟩
  set c : (E n × ℝ) × E n := (0, y)
  have hcomp : (fun z : E n × ℝ => Φ (z, y)) =
      (fun w : (E n × ℝ) × E n => Φ (w + c)) ∘
        (ContinuousLinearMap.inl ℝ (E n × ℝ) (E n)) := by
    funext z; simp [c]
  have hΦc : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E n × ℝ) × E n => Φ (w + c)) :=
    hΦ.comp (contDiff_id.add contDiff_const)
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ hΦc _ (by exact_mod_cast le_top)]
  have hshift := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := Φ) k c
    ((ContinuousLinearMap.inl ℝ (E n × ℝ) (E n)) z)
  rw [hshift]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _i : Fin k, ‖ContinuousLinearMap.inl ℝ (E n × ℝ) (E n)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _)
      (fun _ _ => ContinuousLinearMap.norm_inl_le_one _ _ _)
  have hmem : (ContinuousLinearMap.inl ℝ (E n × ℝ) (E n)) z + c ∈ closedBall 0 Λ := by
    simp only [c, ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add,
      mem_closedBall, dist_zero_right, Prod.norm_def]
    exact max_le hz.le hy
  have := hD _ hmem
  calc _ ≤ ‖iteratedFDeriv ℝ k Φ ((ContinuousLinearMap.inl ℝ (E n × ℝ) (E n)) z + c)‖ * 1 := by
          gcongr
    _ ≤ D := by rw [mul_one]; exact this

lemma rpow_anti {x y z : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hz : z ≤ 0) : y ^ z ≤ x ^ z := by
  rw [show z = -(-z) by ring, Real.rpow_neg (by linarith), Real.rpow_neg hx.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hx _) (Real.rpow_le_rpow hx.le hxy (by linarith))

/-! ## One piece -/
lemma ennreal_arith (C A Rp Rn : ℝ) (hA : 0 ≤ A) (hRp : 0 ≤ Rp) (hRn : 0 ≤ Rn) (h : Rn ≤ Rp) :
    ENNReal.ofReal C * (ENNReal.ofReal Rp * ENNReal.ofReal A) + ENNReal.ofReal (C * Rn) ≤
      ENNReal.ofReal (max C 0 * (A + 1) * Rp) := by
  have hC := le_max_left C 0
  have hC0 := le_max_right C 0
  calc ENNReal.ofReal C * (ENNReal.ofReal Rp * ENNReal.ofReal A) + ENNReal.ofReal (C * Rn)
      ≤ ENNReal.ofReal (max C 0) * (ENNReal.ofReal Rp * ENNReal.ofReal A) +
          ENNReal.ofReal (max C 0 * Rp) := by
        gcongr
    _ = ENNReal.ofReal (max C 0 * (A + 1) * Rp) := by
        rw [← ENNReal.ofReal_mul hRp, ← ENNReal.ofReal_mul hC0, ← ENNReal.ofReal_add
          (by positivity) (by positivity)]
        congr 1; ring

set_option maxHeartbeats 2000000 in
theorem piece_bound (hn : 2 ≤ n) (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤) (δ : ℝ) (hδ : 0 ≤ δ)
    (A : ℝ≥0) (hA : ∀ f : 𝓢(E n, ℂ), eLpNorm (bochnerRiesz δ (f : E n → ℂ)) p volume ≤
      A * eLpNorm f p volume)
    (hneg : δ + ((n : ℝ) - 1) / 2 + 1 - n < 0)
    (x₀ y₀ : E n) (r : ℝ) (hr : 0 < r) (hsep : 6 * r ≤ ‖x₀ - y₀‖)
    (ψ : E n → E n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ))
    (hψs : ∀ x y, ψ x y ≠ 0 → x ∈ ball x₀ r ∧ y ∈ ball y₀ r) :
    ∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ f : 𝓢(E n, ℂ),
      eLpNorm (carlesonSjolinOp ψ R f) p volume ≤
        C * ENNReal.ofReal (R ^ (δ + ((n : ℝ) - 1) / 2 + 1 - n)) * eLpNorm f p volume := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set μ := δ + ((n : ℝ) - 1) / 2 with hμdef
  have hμ0 : 0 < μ := by rw [hμdef]; linarith
  set ν := (n : ℝ) - μ - 1 with hνdef
  have hν : 0 < ν := by rw [hνdef]; linarith
  set e := μ + 1 - n with hedef
  have hen : -(n : ℝ) ≤ e := by rw [hedef]; linarith
  obtain ⟨c, hc0, hc⟩ := Kfun_eq_radial hn δ hδ
  set d := ‖x₀ - y₀‖ with hd
  set ρ₁ := 2 * r with hρ₁
  set ρ₂ := d + 4 * r with hρ₂
  have hρ₁0 : 0 < ρ₁ := by positivity
  have hρ₁₂ : ρ₁ < ρ₂ := by rw [hρ₁, hρ₂]; linarith [norm_nonneg (x₀ - y₀)]
  set h := 1 / (16 * ρ₂) with hhdef
  have hh0 : 0 < h := by positivity
  have hρ₂0 : 0 < ρ₂ := by linarith
  have hhρ : h * (4 * ρ₂) < 1 / 2 := by
    rw [hhdef, show 1 / (16 * ρ₂) * (4 * ρ₂) = 1 / 4 by field_simp; ring]; norm_num
  obtain ⟨τ₁, hτ₁, hhτ₁, hD⟩ := D_ne μ ν c h (ρ₁ / 4) (4 * ρ₂) hμ0 hc0 (by positivity) hh0 hhρ
  obtain ⟨g, hg, hgid, hgb⟩ := exists_clamp (ρ₁ ^ 2) (ρ₂ ^ 2) (ρ₁ ^ 2 / 2)
    (by nlinarith) (by positivity)
  obtain ⟨κ, hκ, hκid, hκb⟩ := exists_clamp (-(τ₁ / 4)) (τ₁ / 4) (τ₁ / 4) (by linarith)
    (by positivity)
  -- the clamped distance
  set ρt : E n → E n → ℝ := fun x y => Real.sqrt (g (‖x - y‖ ^ 2)) with hρtdef
  have hgpos : ∀ s, 0 < g s := fun s => by nlinarith [(hgb s).1]
  have hρt_lo : ∀ x y, ρ₁ / 2 ≤ ρt x y := fun x y => by
    rw [hρtdef]; apply Real.le_sqrt_of_sq_le; nlinarith [(hgb (‖x - y‖ ^ 2)).1]
  have hρt_hi : ∀ x y, ρt x y ≤ 2 * ρ₂ := fun x y => by
    rw [hρtdef, Real.sqrt_le_left (by positivity)]; nlinarith [(hgb (‖x - y‖ ^ 2)).2]
  have hρt_eq : ∀ x y, ρ₁ ≤ ‖x - y‖ → ‖x - y‖ ≤ ρ₂ → ρt x y = ‖x - y‖ := fun x y h1 h2 => by
    show √(g (‖x - y‖ ^ 2)) = _
    rw [hgid _ (by nlinarith) (by nlinarith [norm_nonneg (x - y)]),
      Real.sqrt_sq (norm_nonneg _)]
  have hρt_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun w : E n × E n => ρt w.1 w.2) :=
    (hg.comp ((contDiff_fst.sub contDiff_snd).norm_sq ℝ)).sqrt (fun w => (hgpos _).ne')
  -- the amplitude factors
  set T : Set (ℝ × ℝ) := {q | q.1 ∈ Set.Ioo (ρ₁ / 4) (4 * ρ₂) ∧ |q.2| < τ₁} with hTdef
  have hTΩ : ∀ q ∈ T, q ∈ Ω h ∧ Df μ ν c h q.1 q.2 ≠ 0 := fun q hq =>
    hD q.1 ⟨hq.1.1.le, hq.1.2.le⟩ q.2 hq.2.le
  have hTopen : IsOpen T := by
    apply IsOpen.inter
    · exact isOpen_Ioo.preimage continuous_fst
    · exact isOpen_lt (continuous_abs.comp continuous_snd) continuous_const
  have hTsub : T ⊆ Ω h := fun q hq => (hTΩ q hq).1
  set F₀ : ℝ × ℝ → ℂ := fun q =>
    starRingEnd ℂ (ex (h * q.1) * Pf μ ν c h q.1 q.2) * (Df μ ν c h q.1 q.2)⁻¹ with hF₀
  set Fh : ℝ × ℝ → ℂ := fun q =>
    -starRingEnd ℂ (Pf μ ν c 0 q.1 q.2) * (Df μ ν c h q.1 q.2)⁻¹ with hFh
  have hΩ0 : Ω h ⊆ Ω 0 := fun q hq => ⟨hq.1, by simp⟩
  have hF₀s : ContDiffOn ℝ (⊤ : ℕ∞) F₀ T := by
    have he : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => ex (h * q.1)) T :=
      (ex_contDiff.comp (contDiff_const.mul contDiff_fst)).contDiffOn
    exact (conj_contDiff.comp_contDiffOn (he.mul ((Pf_contDiffOn μ ν c h hμ0).mono hTsub))).mul
      (((Df_contDiffOn μ ν c h hμ0).mono hTsub).inv (fun q hq => (hTΩ q hq).2))
  have hFhs : ContDiffOn ℝ (⊤ : ℕ∞) Fh T :=
    ((conj_contDiff.comp_contDiffOn ((Pf_contDiffOn μ ν c 0 hμ0).mono
      (hTsub.trans hΩ0))).neg).mul
      (((Df_contDiffOn μ ν c h hμ0).mono hTsub).inv (fun q hq => (hTΩ q hq).2))
  have hrange : ∀ x y τ, (ρt x y, κ τ) ∈ T := fun x y τ => by
    refine ⟨⟨by linarith [hρt_lo x y], by linarith [hρt_hi x y]⟩, ?_⟩
    rw [abs_lt]; constructor <;> linarith [(hκb τ).1, (hκb τ).2]
  set Kc : Set (ℝ × ℝ) := Set.Icc (ρ₁ / 2) (2 * ρ₂) ×ˢ Set.Icc (-(τ₁ / 2)) (τ₁ / 2)
  have hKcT : Kc ⊆ T := by
    rintro ⟨a, b⟩ ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    rw [abs_lt]; constructor <;> linarith
  have hrangeK : ∀ x y τ, (ρt x y, κ τ) ∈ Kc := fun x y τ =>
    ⟨⟨hρt_lo x y, hρt_hi x y⟩, by linarith [(hκb τ).1], by linarith [(hκb τ).2]⟩
  obtain ⟨MF₀, hMF₀⟩ := (isCompact_Icc.prod isCompact_Icc : IsCompact Kc).exists_bound_of_continuousOn
    (hF₀s.continuousOn.mono hKcT)
  obtain ⟨MFh, hMFh⟩ := (isCompact_Icc.prod isCompact_Icc : IsCompact Kc).exists_bound_of_continuousOn
    (hFhs.continuousOn.mono hKcT)
  -- ψ is bounded with compact support
  have hψcs : HasCompactSupport (Function.uncurry ψ) := by
    apply HasCompactSupport.intro ((isCompact_closedBall x₀ r).prod (isCompact_closedBall y₀ r))
    intro z hz
    by_contra hne
    obtain ⟨h1, h2⟩ := hψs z.1 z.2 hne
    exact hz ⟨ball_subset_closedBall h1, ball_subset_closedBall h2⟩
  obtain ⟨Mψ, hMψ⟩ := hψ.continuous.bounded_above_of_compact_support hψcs
  have hMψ0 : 0 ≤ Mψ := (norm_nonneg _).trans (hMψ (x₀, y₀))
  -- bound on A over [0, 1/ρ₁]
  obtain ⟨SA, hSA⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (1 / ρ₁))).exists_bound_of_continuousOn
    (Aμ_contDiff μ hμ0).continuous.continuousOn
  have hSA0 : 0 ≤ SA := (norm_nonneg _).trans (hSA 0 ⟨le_rfl, by positivity⟩)
  -- the localized kernels
  obtain ⟨χ₁, hχ₁i, hχ₁o⟩ : ∃ χ : ContDiffBump x₀, χ.rIn = r ∧ χ.rOut = 2 * r :=
    ⟨⟨r, 2 * r, hr, by linarith⟩, rfl, rfl⟩
  obtain ⟨χ₂, hχ₂i, hχ₂o⟩ : ∃ χ : ContDiffBump y₀, χ.rIn = r ∧ χ.rOut = 2 * r :=
    ⟨⟨r, 2 * r, hr, by linarith⟩, rfl, rfl⟩
  have hχ₁ : ∀ x, χ₁ x ≠ 0 → x ∈ ball x₀ (2 * r) := fun x hx => by
    by_contra h'
    exact hx (χ₁.zero_of_le_dist (by rw [hχ₁o]; simpa [mem_ball, dist_comm] using h'))
  have hχ₂ : ∀ y, χ₂ y ≠ 0 → y ∈ ball y₀ (2 * r) := fun y hy => by
    by_contra h'
    exact hy (χ₂.zero_of_le_dist (by rw [hχ₂o]; simpa [mem_ball, dist_comm] using h'))
  have hχ₁1 : ∀ x ∈ ball x₀ r, χ₁ x = 1 := fun x hx =>
    χ₁.one_of_mem_closedBall (by rw [hχ₁i]; exact ball_subset_closedBall hx)
  have hχ₂1 : ∀ y ∈ ball y₀ r, χ₂ y = 1 := fun y hy =>
    χ₂.one_of_mem_closedBall (by rw [hχ₂i]; exact ball_subset_closedBall hy)
  have hdist : ∀ x y, x ∈ ball x₀ (2 * r) → y ∈ ball y₀ (2 * r) → ρ₁ ≤ ‖x - y‖ := by
    intro x y hx hy
    rw [mem_ball, dist_eq_norm] at hx hy
    have : ‖x₀ - y₀‖ ≤ ‖x₀ - x‖ + ‖x - y‖ + ‖y - y₀‖ := by
      calc ‖x₀ - y₀‖ = ‖(x₀ - x) + (x - y) + (y - y₀)‖ := by congr 1; abel
        _ ≤ _ := (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    rw [norm_sub_rev x₀ x] at this
    rw [hρ₁]; linarith
  set Kj : ℝ → ℝ → E n → E n → ℂ := fun hj R x y =>
    ((χ₁ x * χ₂ y * (max R 1) ^ e * (max R 1 + hj) ^ n : ℝ) : ℂ) *
      Kfun n δ ((max R 1 + hj) • (x - y)) with hKjdef
  have hKcont : ∀ hj R, Continuous (Function.uncurry (Kj hj R)) := fun hj R => by
    have hK := Kfun_continuous (n := n) δ hδ
    have h1 : Continuous (fun w : E n × E n => χ₁ w.1) := χ₁.continuous.comp continuous_fst
    have h2 : Continuous (fun w : E n × E n => χ₂ w.2) := χ₂.continuous.comp continuous_snd
    show Continuous (fun w : E n × E n =>
      ((χ₁ w.1 * χ₂ w.2 * (max R 1) ^ e * (max R 1 + hj) ^ n : ℝ) : ℂ) *
        Kfun n δ ((max R 1 + hj) • (w.1 - w.2)))
    have h3 : Continuous (fun w : E n × E n => Kfun n δ ((max R 1 + hj) • (w.1 - w.2))) :=
      hK.comp (by fun_prop)
    have h4 : Continuous (fun w : E n × E n =>
        ((χ₁ w.1 * χ₂ w.2 * (max R 1) ^ e * (max R 1 + hj) ^ n : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (((h1.mul h2).mul continuous_const).mul continuous_const)
    exact h4.mul h3
  have hKsupp : ∀ hj R x y, Kj hj R x y ≠ 0 → x ∈ ball x₀ (2 * r) ∧ y ∈ ball y₀ (2 * r) := by
    intro hj R x y hK
    have : χ₁ x * χ₂ y ≠ 0 := by
      intro h0; apply hK; simp only [hKjdef, h0, zero_mul, Complex.ofReal_zero]
    exact ⟨hχ₁ x (left_ne_zero_of_mul this), hχ₂ y (right_ne_zero_of_mul this)⟩
  -- the kernel formula on the support
  have hKform : ∀ hj, 0 ≤ hj → ∀ R x y, ρ₁ ≤ ‖x - y‖ →
      Kj hj R x y = ((χ₁ x * χ₂ y : ℝ) : ℂ) *
        (ex (max R 1 * ‖x - y‖) * ex (hj * ‖x - y‖) * Pf μ ν c hj ‖x - y‖ (max R 1)⁻¹ +
          starRingEnd ℂ (ex (max R 1 * ‖x - y‖) * ex (hj * ‖x - y‖) *
            Pf μ ν c hj ‖x - y‖ (max R 1)⁻¹)) := by
    intro hj hj0 R x y hxy
    rw [← kernel_formula δ μ c hμdef hμ0 hc (max R 1) hj (by positivity) hj0 (x - y)
      (by linarith)]
    show ((χ₁ x * χ₂ y * (max R 1) ^ e * (max R 1 + hj) ^ n : ℝ) : ℂ) * _ = _
    rw [← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    ring
  have hPf_le : ∀ hj, 0 ≤ hj → hj ≤ h → ∀ R ρ, ρ₁ ≤ ρ →
      ‖Pf μ ν c hj ρ (max R 1)⁻¹‖ ≤ |c| * ρ₁ ^ (-μ - 1) * (1 + h) ^ ν * SA := by
    intro hj hj0 hjh R ρ hρ
    have hR1 : 1 ≤ max R 1 := le_max_right _ _
    have hRi : (max R 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1
    have hRi0 : 0 ≤ (max R 1)⁻¹ := by positivity
    have hρ0 : 0 < ρ := by linarith
    have hq : 1 ≤ 1 + hj * (max R 1)⁻¹ := by nlinarith
    rw [Pf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hρ0 _), abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
    have harg : (max R 1)⁻¹ / ((1 + hj * (max R 1)⁻¹) * ρ) ∈ Set.Icc (0 : ℝ) (1 / ρ₁) := by
      constructor
      · positivity
      · rw [div_le_div_iff₀ (by positivity) hρ₁0, one_mul]
        nlinarith
    have h1 : ρ ^ (-μ - 1) ≤ ρ₁ ^ (-μ - 1) := rpow_anti hρ₁0 hρ (by linarith)
    have h2 : (1 + hj * (max R 1)⁻¹) ^ ν ≤ (1 + h) ^ ν :=
      Real.rpow_le_rpow (by linarith) (by nlinarith) hν.le
    have h3 := hSA _ harg
    gcongr
  set M : ℝ := 2 * (|c| * ρ₁ ^ (-μ - 1) * (1 + h) ^ ν * SA) with hMdef
  have hKbound : ∀ hj, 0 ≤ hj → hj ≤ h → ∀ R x y, ‖Kj hj R x y‖ ≤ M := by
    intro hj hj0 hjh R x y
    by_cases hK0 : Kj hj R x y = 0
    · rw [hK0, norm_zero]; positivity
    obtain ⟨hx, hy⟩ := hKsupp hj R x y hK0
    have hxy := hdist x y hx hy
    rw [hKform hj hj0 R x y hxy, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hχ : |χ₁ x * χ₂ y| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg χ₁.nonneg, abs_of_nonneg χ₂.nonneg]
      exact mul_le_one₀ χ₁.le_one χ₂.nonneg χ₂.le_one
    have hZ := hPf_le hj hj0 hjh R ‖x - y‖ hxy
    calc |χ₁ x * χ₂ y| * ‖_ + _‖ ≤ 1 * (‖ex (max R 1 * ‖x - y‖) * ex (hj * ‖x - y‖) *
          Pf μ ν c hj ‖x - y‖ (max R 1)⁻¹‖ + ‖ex (max R 1 * ‖x - y‖) * ex (hj * ‖x - y‖) *
          Pf μ ν c hj ‖x - y‖ (max R 1)⁻¹‖) := by
          gcongr
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [Complex.norm_conj]
      _ ≤ M := by
          rw [norm_mul, norm_mul, norm_ex, norm_ex, one_mul, one_mul, one_mul, hMdef]
          linarith
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  set Λ : ℝ := ‖x₀‖ + ‖y₀‖ + 2 * r + τ₁ + 1 with hΛ
  have hKnorm : ∀ hj R x y, Kj hj R x y ≠ 0 → ‖x‖ ≤ Λ ∧ ‖y‖ ≤ Λ := by
    intro hj R x y hK
    obtain ⟨hx, hy⟩ := hKsupp hj R x y hK
    rw [mem_ball, dist_eq_norm] at hx hy
    have h1 := norm_le_norm_add_norm_sub' x x₀
    have h2 := norm_le_norm_add_norm_sub' y y₀
    constructor <;> linarith [norm_nonneg x₀, norm_nonneg y₀]
  -- BR bounds the localized kernels
  have hKop : ∀ hj, 0 ≤ hj → hj ≤ h → ∀ R,
      opNorm p p (kernelOp (Kj hj R)) ≤ ENNReal.ofReal ((max R 1) ^ e) * A := by
    intro hj hj0 hjh R
    have hR1 : 1 ≤ max R 1 := le_max_right _ _
    apply opNorm_le_of_schwartz p hp hpt (Kj hj R) (hKcont hj R) M Λ (hKbound hj hj0 hjh R)
      (hKnorm hj R) _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top)
    intro g
    set u : E n → ℂ := fun y => (χ₂ y : ℂ) * g y with hu
    have huc : HasCompactSupport u := (χ₂.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
    have hus : ContDiff ℝ (⊤ : ℕ∞) u :=
      (Complex.ofRealCLM.contDiff.comp χ₂.contDiff).mul (g.smooth ⊤)
    set gs : 𝓢(E n, ℂ) := huc.toSchwartzMap hus
    have hgs : (gs : E n → ℂ) = u := rfl
    set I : E n → ℂ := fun x => ∫ y, (((max R 1 + hj) ^ n : ℝ) : ℂ) *
      Kfun n δ ((max R 1 + hj) • (x - y)) * gs y with hI
    have hrepr : ∀ x, kernelOp (Kj hj R) g x = ((χ₁ x * (max R 1) ^ e : ℝ) : ℂ) * I x := by
      intro x
      simp only [kernelOp, hI, hgs, hu]
      rw [← integral_const_mul]
      congr 1; funext y
      show ((χ₁ x * χ₂ y * (max R 1) ^ e * (max R 1 + hj) ^ n : ℝ) : ℂ) * _ * _ = _
      push_cast; ring
    have h1 : eLpNorm (kernelOp (Kj hj R) g) p volume ≤
        eLpNorm (fun x => (((max R 1) ^ e : ℝ) : ℂ) • I x) p volume := by
      apply eLpNorm_mono
      intro x
      rw [hrepr, norm_mul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_mul]
      have : |χ₁ x| ≤ 1 := by rw [abs_of_nonneg χ₁.nonneg]; exact χ₁.le_one
      have h0 : 0 ≤ |(max R 1) ^ e| := abs_nonneg _
      calc |χ₁ x| * |(max R 1) ^ e| * ‖I x‖ ≤ 1 * |(max R 1) ^ e| * ‖I x‖ := by gcongr
        _ = _ := by ring
    have h2 := dil_bound p hp hpt δ hδ A hA (max R 1 + hj) (by positivity) gs
    have h3 : eLpNorm gs p volume ≤ eLpNorm g p volume := by
      apply eLpNorm_mono; intro y
      rw [hgs, hu, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg χ₂.nonneg]
      exact mul_le_of_le_one_left (norm_nonneg _) χ₂.le_one
    rw [show (fun x => (((max R 1) ^ e : ℝ) : ℂ) • I x) = (((max R 1) ^ e : ℝ) : ℂ) • I from rfl,
      eLpNorm_const_smul] at h1
    refine h1.trans ?_
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_assoc]
    gcongr
    exact h2.trans (by gcongr)
  -- the amplitudes `b = ψ · F(ρ̃, κ τ)`
  have hΦ : ∀ F : ℝ × ℝ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) F T →
      ContDiff ℝ (⊤ : ℕ∞) (fun w : (E n × ℝ) × E n =>
        ((ψ w.1.1 w.2 : ℝ) : ℂ) * F (ρt w.1.1 w.2, κ w.1.2)) := by
    intro F hF
    have hψ' : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E n × ℝ) × E n => ((ψ w.1.1 w.2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp
        (hψ.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd))
    have hin : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E n × ℝ) × E n => (ρt w.1.1 w.2, κ w.1.2)) :=
      (hρt_smooth.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)).prodMk
        (hκ.comp (contDiff_snd.comp contDiff_fst))
    exact hψ'.mul (hF.comp_contDiff hin (fun w => hrange _ _ _))
  have hbcont : ∀ F : ℝ × ℝ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) F T → ∀ τ,
      Continuous (Function.uncurry fun x y => ((ψ x y : ℝ) : ℂ) * F (ρt x y, κ τ)) := by
    intro F hF τ
    exact (hΦ F hF).continuous.comp
      (show Continuous (fun z : E n × E n => ((z.1, τ), z.2)) by fun_prop)
  have hbbound : ∀ F : ℝ × ℝ → ℂ, ∀ MF, (∀ q ∈ Kc, ‖F q‖ ≤ MF) → ∀ x y τ,
      ‖((ψ x y : ℝ) : ℂ) * F (ρt x y, κ τ)‖ ≤ Mψ * MF := by
    intro F MF hMF x y τ
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul (hMψ (x, y)) (hMF _ (hrangeK x y τ)) (norm_nonneg _) hMψ0
  have hMFnn : ∀ F : ℝ × ℝ → ℂ, ∀ MF, (∀ q ∈ Kc, ‖F q‖ ≤ MF) → 0 ≤ MF := fun F MF hMF =>
    (norm_nonneg _).trans (hMF _ (hrangeK x₀ x₀ 0))
  -- Lemma 2.1
  have hL21 : ∀ hj (F : ℝ × ℝ → ℂ) MF, 0 ≤ hj → hj ≤ h → ContDiffOn ℝ (⊤ : ℕ∞) F T →
      (∀ q ∈ Kc, ‖F q‖ ≤ MF) → ∃ C R₀ : ℝ, ∀ R, R₀ ≤ R →
        opNorm p p (kernelOp fun x y => Kj hj R x y * (((ψ x y : ℝ) : ℂ) * F (ρt x y, κ R⁻¹))) ≤
          ENNReal.ofReal C * opNorm p p (kernelOp (Kj hj R)) +
            ENNReal.ofReal (C * R ^ (-(n : ℝ))) := by
    intro hj F MF hj0 hjh hF hMF
    have hS : IsCompact (closedBall x₀ (2 * r) ×ˢ closedBall y₀ (2 * r)) :=
      (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
    obtain ⟨C, R₀, hCR⟩ := TaoBR.opNorm_le_of_contDiff n p p hp hp (Kj hj)
      (closedBall x₀ (2 * r) ×ˢ closedBall y₀ (2 * r)) hS M
      (fun R => (hKcont hj R).measurable)
      (fun R x y => ⟨hKbound hj hj0 hjh R x y, fun hK => by
        obtain ⟨a, b⟩ := hKsupp hj R x y hK
        exact ⟨ball_subset_closedBall a, ball_subset_closedBall b⟩⟩)
      (fun x y τ => ((ψ x y : ℝ) : ℂ) * F (ρt x y, κ τ))
      (fun τ => (hbcont F hF τ).measurable) (Mψ * MF) (hbbound F MF hMF)
      (τ₁ / 4) (by positivity) (ball (0 : E n × ℝ) Λ) isOpen_ball
      (by
        rintro ⟨x, τ⟩ ⟨⟨⟨x', y'⟩, ⟨hx', -⟩, rfl⟩, hτ⟩
        simp only [mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs]
        simp only [mem_closedBall, dist_eq_norm] at hx'
        have h1 := norm_le_norm_add_norm_sub' x' x₀
        have := hτ.1; have := hτ.2
        refine max_lt (by linarith [norm_nonneg y₀]) ?_
        rw [abs_lt]; constructor <;> linarith [norm_nonneg x₀, norm_nonneg y₀])
      (fun y _ => ((hΦ F hF).comp (contDiff_id.prodMk contDiff_const)).contDiffOn)
      (by
        intro k
        obtain ⟨D, hD⟩ := der_bound _ (hΦ F hF) Λ k
        refine ⟨D, ?_⟩
        rintro y ⟨⟨x', y'⟩, ⟨-, hy'⟩, rfl⟩ z hz
        rw [iteratedFDerivWithin_of_isOpen k isOpen_ball hz]
        simp only [mem_closedBall, dist_eq_norm] at hy'
        have h1 := norm_le_norm_add_norm_sub' y' y₀
        exact hD y' (by linarith [norm_nonneg x₀]) z (by simpa using hz))
      (n : ℝ) (by positivity)
    exact ⟨C, R₀, hCR⟩
  -- the kernel identity: two frequencies separate `e^{+}` from `e^{-}`
  have hid : ∀ R, max 1 (4 / τ₁) ≤ R → ∀ x y,
      ex (R * ‖x - y‖) * ((ψ x y : ℝ) : ℂ) =
        Kj 0 R x y * (((ψ x y : ℝ) : ℂ) * F₀ (ρt x y, κ R⁻¹)) +
          Kj h R x y * (((ψ x y : ℝ) : ℂ) * Fh (ρt x y, κ R⁻¹)) := by
    intro R hR x y
    by_cases h0 : ψ x y = 0
    · simp [h0]
    obtain ⟨hx, hy⟩ := hψs x y h0
    have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hR
    have hRpos : 0 < R := by linarith
    have hRm : max R 1 = R := max_eq_left hR1
    have hxy1 : ρ₁ ≤ ‖x - y‖ :=
      hdist x y (ball_subset_ball (by linarith) hx) (ball_subset_ball (by linarith) hy)
    have hxy2 : ‖x - y‖ ≤ ρ₂ := by
      rw [mem_ball, dist_eq_norm] at hx hy
      have : ‖x - y‖ ≤ ‖x - x₀‖ + ‖x₀ - y₀‖ + ‖y - y₀‖ := by
        calc ‖x - y‖ = ‖(x - x₀) + (x₀ - y₀) - (y - y₀)‖ := by congr 1; abel
          _ ≤ _ := (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      rw [hρ₂]; linarith
    have hRi : R⁻¹ ≤ τ₁ / 4 := by
      rw [inv_le_comm₀ hRpos (by positivity)]
      calc (τ₁ / 4)⁻¹ = 4 / τ₁ := by rw [inv_div]
        _ ≤ R := le_trans (le_max_right _ _) hR
    have hRi0 : 0 < R⁻¹ := inv_pos.2 hRpos
    have hκR : κ R⁻¹ = R⁻¹ := hκid _ (by linarith) hRi
    have hDne : Df μ ν c h ‖x - y‖ R⁻¹ ≠ 0 :=
      (hD ‖x - y‖ ⟨by linarith, by linarith⟩ R⁻¹ (by rw [abs_of_pos hRi0]; linarith)).2
    rw [hρt_eq x y hxy1 hxy2, hκR, hKform 0 le_rfl R x y hxy1, hKform h hh0.le R x y hxy1, hRm,
      hχ₁1 x hx, hχ₂1 y hy]
    have hex0 : ex (0 * ‖x - y‖) = 1 := by simp [ex]
    rw [hex0]
    simp only [hF₀, hFh]
    simp only [Df, map_mul, mul_one, Complex.ofReal_one, one_mul] at hDne ⊢
    generalize ex (R * ‖x - y‖) = E0 at hDne ⊢
    generalize ex (h * ‖x - y‖) = e0 at hDne ⊢
    generalize Pf μ ν c 0 ‖x - y‖ R⁻¹ = P0 at hDne ⊢
    generalize Pf μ ν c h ‖x - y‖ R⁻¹ = Ph at hDne ⊢
    generalize ((ψ x y : ℝ) : ℂ) = q at hDne ⊢
    set D0 := P0 * (starRingEnd ℂ) e0 * (starRingEnd ℂ) Ph - (starRingEnd ℂ) P0 * e0 * Ph with hD0
    have hD' : D0 ≠ 0 := by rw [hD0]; convert hDne using 1; ring
    calc E0 * q = E0 * q * D0 * D0⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hD', mul_one]
      _ = _ := by rw [hD0]; ring
  -- assembly
  obtain ⟨MF₀', hMF₀'⟩ : ∃ m, ∀ q ∈ Kc, ‖F₀ q‖ ≤ m := ⟨MF₀, hMF₀⟩
  obtain ⟨MFh', hMFh'⟩ : ∃ m, ∀ q ∈ Kc, ‖Fh q‖ ≤ m := ⟨MFh, hMFh⟩
  obtain ⟨C₀, R₀₀, hC₀⟩ := hL21 0 F₀ MF₀' le_rfl hh0.le hF₀s hMF₀'
  obtain ⟨Ch, R₀h, hCh⟩ := hL21 h Fh MFh' hh0.le le_rfl hFhs hMFh'
  obtain ⟨CT, hCT⟩ := trivial_bound p hp hpt ψ hψ.continuous hψcs
  set R₂ := max (max R₀₀ R₀h) (max 1 (4 / τ₁)) with hR₂
  have hR₂1 : 1 ≤ R₂ := le_trans (le_max_left _ _) (le_max_right _ _)
  set Cfin : ℝ := (max C₀ 0 + max Ch 0) * ((A : ℝ) + 1) + (CT : ℝ) * R₂ ^ ν with hCfin
  have hCfin0 : 0 ≤ Cfin := by positivity
  refine ⟨Cfin.toNNReal, fun R hR f => ?_⟩
  have hRpos : 0 < R := by linarith
  have hcoe : ((Cfin.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal Cfin := rfl
  rw [hcoe, ← ENNReal.ofReal_mul hCfin0]
  rcases lt_or_ge R R₂ with hRR | hRR
  · -- small `R`: the trivial bound
    refine (hCT R f).trans ?_
    gcongr
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    have h1 : R₂ ^ e ≤ R ^ e := rpow_anti hRpos hRR.le hneg.le
    have h2 : R₂ ^ ν * R₂ ^ e = 1 := by
      rw [← Real.rpow_add (by linarith), show ν + e = 0 by rw [hνdef, hedef]; ring,
        Real.rpow_zero]
    have h3 : 0 ≤ (CT : ℝ) := CT.2
    have h4 : 0 ≤ R₂ ^ ν := by positivity
    calc (CT : ℝ) = CT * (R₂ ^ ν * R₂ ^ e) := by rw [h2, mul_one]
      _ ≤ CT * (R₂ ^ ν * R ^ e) := by gcongr
      _ ≤ Cfin * R ^ e := by
          rw [hCfin, add_mul, ← mul_assoc]
          have : 0 ≤ (max C₀ 0 + max Ch 0) * ((A : ℝ) + 1) * R ^ e := by positivity
          linarith
  · -- large `R`: two applications of Lemma 2.1
    have hRbig : max 1 (4 / τ₁) ≤ R := le_trans (le_max_right _ _) hRR
    have hR00 : R₀₀ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hRR
    have hR0h : R₀h ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hRR
    have hRm : max R 1 = R := max_eq_left hR
    set k₀ : E n → E n → ℂ := fun x y => Kj 0 R x y * (((ψ x y : ℝ) : ℂ) * F₀ (ρt x y, κ R⁻¹))
    set kh : E n → E n → ℂ := fun x y => Kj h R x y * (((ψ x y : ℝ) : ℂ) * Fh (ρt x y, κ R⁻¹))
    have hk₀c : Continuous (Function.uncurry k₀) :=
      (hKcont 0 R).mul (hbcont F₀ hF₀s R⁻¹)
    have hkhc : Continuous (Function.uncurry kh) :=
      (hKcont h R).mul (hbcont Fh hFhs R⁻¹)
    have hkM : ∀ hj, 0 ≤ hj → hj ≤ h → ∀ F : ℝ × ℝ → ℂ, ∀ MF, (∀ q ∈ Kc, ‖F q‖ ≤ MF) → ∀ x y,
        ‖Kj hj R x y * (((ψ x y : ℝ) : ℂ) * F (ρt x y, κ R⁻¹))‖ ≤ M * (Mψ * MF) := by
      intro hj hj0 hjh F MF hMF x y
      rw [norm_mul]
      exact mul_le_mul (hKbound hj hj0 hjh R x y) (hbbound F MF hMF x y R⁻¹) (norm_nonneg _) hM0
    have hkS : ∀ hj (F : ℝ × ℝ → ℂ) x y, Kj hj R x y * (((ψ x y : ℝ) : ℂ) * F (ρt x y, κ R⁻¹)) ≠ 0 →
        ‖x‖ ≤ Λ ∧ ‖y‖ ≤ Λ := fun hj F x y hne => hKnorm hj R x y (left_ne_zero_of_mul hne)
    have hsplit : carlesonSjolinOp ψ R f = kernelOp k₀ f + kernelOp kh f := by
      funext x
      simp only [carlesonSjolinOp, kernelOp, Pi.add_apply]
      rw [← integral_add (kernelOp_integrable p hp k₀ hk₀c _ Λ (hkM 0 le_rfl hh0.le F₀ MF₀' hMF₀')
          (hkS 0 F₀) f (f.memLp p volume) x)
        (kernelOp_integrable p hp kh hkhc _ Λ (hkM h hh0.le le_rfl Fh MFh' hMFh')
          (hkS h Fh) f (f.memLp p volume) x)]
      congr 1; funext y
      rw [← add_mul, ← hid R hRbig x y]
      rfl
    have hRe : R ^ (-(n : ℝ)) ≤ R ^ e := Real.rpow_le_rpow_of_exponent_le hR hen
    have hbound : ∀ hj, 0 ≤ hj → hj ≤ h → ∀ (k : E n → E n → ℂ) (C : ℝ),
        opNorm p p (kernelOp k) ≤ ENNReal.ofReal C * opNorm p p (kernelOp (Kj hj R)) +
          ENNReal.ofReal (C * R ^ (-(n : ℝ))) →
        eLpNorm (kernelOp k f) p volume ≤
          ENNReal.ofReal (max C 0 * ((A : ℝ) + 1) * R ^ e) * eLpNorm f p volume := by
      intro hj hj0 hjh k C hk
      have hk' : opNorm p p (kernelOp k) ≤
          ENNReal.ofReal (max C 0 * ((A : ℝ) + 1) * R ^ e) := by
        refine hk.trans ?_
        have := hKop hj hj0 hjh R
        rw [hRm, ← ENNReal.ofReal_coe_nnreal] at this
        refine le_trans ?_ (ennreal_arith C A (R ^ e) (R ^ (-(n : ℝ))) A.2 (by positivity)
          (by positivity) hRe)
        gcongr
      exact eLpNorm_le_opNorm hk' ENNReal.ofReal_ne_top (by funext x; simp [kernelOp])
        (f.memLp p volume)
    have hb₀ := hbound 0 le_rfl hh0.le k₀ C₀ (hC₀ R hR00)
    have hbh := hbound h hh0.le le_rfl kh Ch (hCh R hR0h)
    rw [hsplit]
    refine (eLpNorm_add_le (kernelOp_aesm k₀ hk₀c _ f.continuous.aestronglyMeasurable)
      (kernelOp_aesm kh hkhc _ f.continuous.aestronglyMeasurable) hp).trans ?_
    refine (add_le_add hb₀ hbh).trans ?_
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    gcongr
    rw [hCfin]
    have : 0 ≤ (CT : ℝ) * R₂ ^ ν * R ^ e := by have := CT.2; positivity
    nlinarith

end TaoBR.CS.PartP
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR
namespace CS
variable {n : ℕ}
/-! ## Part P: one piece -/
alias piece_bound := TaoBR.CS.PartP.piece_bound

end CS
end TaoBR
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace Manifold
namespace TaoBR.CS.PartM
variable {n : ℕ}
theorem carlesonSjolinOp_sum {ι : Type} [Fintype ι] (ψs : ι → E n → E n → ℝ)
    (hψ : ∀ i, Continuous (Function.uncurry (ψs i)))
    (hψc : ∀ i, HasCompactSupport (Function.uncurry (ψs i))) (R : ℝ) (f : 𝓢(E n, ℂ)) :
    carlesonSjolinOp (fun x y => ∑ i, ψs i x y) R f = ∑ i, carlesonSjolinOp (ψs i) R f := by
  funext x
  simp only [carlesonSjolinOp, kernelOp, Finset.sum_apply]
  rw [← integral_finsetSum]
  · congr 1; funext y
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
  · intro i _
    obtain ⟨M, hM⟩ := (hψ i).bounded_above_of_compact_support (hψc i)
    refine (f.integrable (μ := volume)).bdd_mul (c := M) ?_ ?_
    · have h1 : Continuous (fun y => ψs i x y) := (hψ i).comp (Continuous.prodMk_right x)
      exact (by fun_prop : Continuous fun y : E n =>
        Complex.exp (2 * Real.pi * Complex.I * ((R * ‖x - y‖ : ℝ) : ℂ)) *
          ((ψs i x y : ℝ) : ℂ)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y => ?_)
      rw [norm_mul, norm_exp_two_pi_I', one_mul, Complex.norm_real]
      exact hM (x, y)

end TaoBR.CS.PartM
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR
namespace CS
variable {n : ℕ}
alias carlesonSjolinOp_sum := TaoBR.CS.PartM.carlesonSjolinOp_sum

end CS
end TaoBR
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace Manifold
namespace TaoBR.CS.PartM
variable {n : ℕ}
theorem exponent_eq (hn : 2 ≤ n) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (hp' : p ≤ ENNReal.ofReal (2 * n / (n + 1))) (α : ℝ) :
    critIndex n p + α + ((n : ℝ) - 1) / 2 + 1 - n = -((n : ℝ) * (conjExp p)⁻¹.toReal) + α := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpt : p ≠ ⊤ := by
    intro h; rw [h] at hp'; exact absurd hp' (by simp)
  have hq1 : p⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hp
  set q := p⁻¹.toReal with hqdef
  have hq : ((n : ℝ) + 1) / (2 * n) ≤ q := by
    have h1 : (ENNReal.ofReal (2 * n / (n + 1)))⁻¹ ≤ p⁻¹ := ENNReal.inv_le_inv.2 hp'
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), inv_div] at h1
    have := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top hq1) h1
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hc : (conjExp p)⁻¹.toReal = 1 - q := by
    rw [conjExp, inv_inv, ENNReal.toReal_sub_of_le hq1 ENNReal.one_ne_top, ENNReal.toReal_one]
  have hge : 0 ≤ (n : ℝ) * (q - 1 / 2) - 1 / 2 := by
    have : (n : ℝ) * q ≥ (n + 1) / 2 := by
      have := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ n)
      rw [mul_div_assoc', mul_comm (n : ℝ) ((n : ℝ) + 1), mul_div_mul_right _ _ (by positivity)] at this
      linarith
    nlinarith
  have habs : |q - 1 / 2| = q - 1 / 2 := by
    rw [abs_of_nonneg]
    nlinarith
  rw [critIndex, hc, ← hqdef, habs, max_eq_left hge]
  ring

theorem exists_pieces (ψ : E n → E n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ))
    (hψc : HasCompactSupport (Function.uncurry ψ))
    (hψd : ∃ c : ℝ, 0 < c ∧ ∀ x y, ψ x y ≠ 0 → c ≤ ‖x - y‖) :
    ∃ (ι : Type) (_ : Fintype ι) (ψs : ι → E n → E n → ℝ) (x₀ y₀ : ι → E n) (r : ℝ), 0 < r ∧
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (ψs i))) ∧
      (∀ i x y, ψs i x y ≠ 0 → x ∈ ball (x₀ i) r ∧ y ∈ ball (y₀ i) r) ∧
      (∀ i, 6 * r ≤ ‖x₀ i - y₀ i‖) ∧
      ∀ x y, ψ x y = ∑ i, ψs i x y := by
  obtain ⟨c, hc, hcd⟩ := hψd
  obtain ⟨L, -, hL⟩ := bounded_support_of_hasCompactSupport ψ hψc
  set r := c / 8 with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact
    (isCompact_closedBall (0 : E n) L) hr0
  haveI : Fintype t := htf.fintype
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E n)
    (isClosed_closedBall (x := (0 : E n)) (ε := L)) (fun i : t => ball (i : E n) r)
    (fun _ => isOpen_ball) (by
      intro x hx
      obtain ⟨i, hi, hx'⟩ := Set.mem_iUnion₂.1 (hcov hx)
      exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hx'⟩)
  have hsm : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => f i x) := fun i => by
    have := (f i).contMDiff
    rw [contMDiff_iff_contDiff] at this
    exact this.of_le (by exact_mod_cast le_top)
  have hsupp : ∀ i x, f i x ≠ 0 → x ∈ ball (i : E n) r := fun i x h =>
    hf i (subset_tsupport _ h)
  have hsum1 : ∀ x ∈ closedBall (0 : E n) L, ∑ i, f i x = 1 := fun x hx => by
    rw [← finsum_eq_sum_of_fintype]; exact f.sum_eq_one hx
  let ι := {ij : t × t // 6 * r ≤ ‖(ij.1 : E n) - ij.2‖}
  refine ⟨ι, inferInstance, fun ij x y => f ij.1.1 x * f ij.1.2 y * ψ x y,
    fun ij => ij.1.1, fun ij => ij.1.2, r, hr0, ?_, ?_, fun ij => ij.2, ?_⟩
  · intro ij
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : E n × E n => f ij.1.1 z.1) :=
      (hsm _).comp contDiff_fst
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z : E n × E n => f ij.1.2 z.2) :=
      (hsm _).comp contDiff_snd
    exact (h1.mul h2).mul hψ
  · intro ij x y h
    exact ⟨hsupp _ x (left_ne_zero_of_mul (left_ne_zero_of_mul h)),
      hsupp _ y (right_ne_zero_of_mul (left_ne_zero_of_mul h))⟩
  · intro x y
    by_cases h0 : ψ x y = 0
    · simp [h0]
    obtain ⟨hx, hy⟩ := hL x y h0
    have hxy := hcd x y h0
    have hfull : ψ x y = ∑ ij : t × t, f ij.1 x * f ij.2 y * ψ x y := by
      have e : ∑ ij : t × t, f ij.1 x * f ij.2 y * ψ x y =
          ((∑ i, f i x) * (∑ j, f j y)) * ψ x y := by
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.sum_mul]
        simp_rw [Finset.sum_mul]
      rw [e, hsum1 y (by simpa using hy), hsum1 x (by simpa using hx)]; ring
    rw [hfull]
    show _ = ∑ ij : ι, f ij.1.1 x * f ij.1.2 y * ψ x y
    rw [← Finset.sum_subtype (Finset.univ.filter
      (fun ij : t × t => 6 * r ≤ ‖(ij.1 : E n) - ij.2‖)) (by simp)
      (fun ij : t × t => f ij.1 x * f ij.2 y * ψ x y)]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun ij _ => ?_)
    split_ifs with hij
    · rfl
    · by_contra hne
      have h1 := hsupp _ x (left_ne_zero_of_mul (left_ne_zero_of_mul hne))
      have h2 := hsupp _ y (right_ne_zero_of_mul (left_ne_zero_of_mul hne))
      rw [mem_ball, dist_eq_norm] at h1 h2
      apply hij
      have : ‖x - y‖ ≤ ‖x - ij.1‖ + ‖(ij.1 : E n) - ij.2‖ + ‖y - ij.2‖ := by
        calc ‖x - y‖ = ‖(x - ij.1) + ((ij.1 : E n) - ij.2) - (y - ij.2)‖ := by congr 1; abel
          _ ≤ _ := by
            refine (norm_sub_le _ _).trans ?_
            gcongr; exact norm_add_le _ _
      linarith

end TaoBR.CS.PartM
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR
namespace CS
variable {n : ℕ}
/-! ## Part U: splitting `ψ` into pieces -/
alias exists_pieces := TaoBR.CS.PartM.exists_pieces

alias exponent_eq := TaoBR.CS.PartM.exponent_eq

theorem critIndex_nonneg (n : ℕ) (p : ℝ≥0∞) : 0 ≤ critIndex n p := le_max_right _ _

end CS
end TaoBR
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR.CS.PartMain
theorem carlesonSjolinOp_le_of_br_dev (n : ℕ) (hn : 2 ≤ n) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (hp' : p ≤ ENNReal.ofReal (2 * n / (n + 1))) (α : ℝ) (hα : 0 ≤ α) (hBR : BR n p α)
    (ψ : E n → E n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ))
    (hψc : HasCompactSupport (Function.uncurry ψ))
    (hψd : ∃ c : ℝ, 0 < c ∧ ∀ x y, ψ x y ≠ 0 → c ≤ ‖x - y‖) :
    ∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ f : 𝓢(E n, ℂ),
      eLpNorm (carlesonSjolinOp ψ R f) p volume ≤
        C * ENNReal.ofReal (R ^ (-((n : ℝ) * (conjExp p)⁻¹.toReal))) * ENNReal.ofReal (R ^ α) *
          eLpNorm f p volume := by
  obtain ⟨A, hA⟩ := hBR
  set δ := critIndex n p + α with hδdef
  have hδ : 0 ≤ δ := add_nonneg (critIndex_nonneg n p) hα
  have hpt : p ≠ ⊤ := by
    intro h; rw [h] at hp'; exact absurd hp' (by simp)
  have hexp := exponent_eq hn p hp hp' α
  suffices H : ∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ f : 𝓢(E n, ℂ),
      eLpNorm (carlesonSjolinOp ψ R f) p volume ≤
        C * ENNReal.ofReal (R ^ (δ + ((n : ℝ) - 1) / 2 + 1 - n)) * eLpNorm f p volume by
    obtain ⟨C, hC⟩ := H
    refine ⟨C, fun R hR f => (hC R hR f).trans (le_of_eq ?_)⟩
    rw [mul_assoc (C : ℝ≥0∞) (ENNReal.ofReal _) (ENNReal.ofReal _),
      ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add (by linarith), hδdef, hexp]
  by_cases hneg : δ + ((n : ℝ) - 1) / 2 + 1 - n < 0
  · obtain ⟨ι, _, ψs, x₀, y₀, r, hr, hψs, hsupp, hsep, hsum⟩ := exists_pieces ψ hψ hψc hψd
    have hpiece := fun i => piece_bound hn p hp hpt δ hδ A hA hneg (x₀ i) (y₀ i) r hr (hsep i)
      (ψs i) (hψs i) (hsupp i)
    choose C hC using hpiece
    have hcs : ∀ i, HasCompactSupport (Function.uncurry (ψs i)) := fun i => by
      apply HasCompactSupport.intro ((isCompact_closedBall (x₀ i) r).prod
        (isCompact_closedBall (y₀ i) r))
      intro z hz
      by_contra h
      obtain ⟨h1, h2⟩ := hsupp i z.1 z.2 h
      exact hz ⟨ball_subset_closedBall h1, ball_subset_closedBall h2⟩
    refine ⟨∑ i, C i, fun R hR f => ?_⟩
    have hψeq : ψ = fun x y => ∑ i, ψs i x y := by funext x y; exact hsum x y
    rw [hψeq, carlesonSjolinOp_sum ψs (fun i => (hψs i).continuous) hcs R f]
    have haesm : ∀ i ∈ Finset.univ, AEStronglyMeasurable (carlesonSjolinOp (ψs i) R f) volume :=
      fun i _ => by
        apply kernelOp_aesm _ _ _ f.continuous.aestronglyMeasurable
        have h1 : Continuous (fun z : E n × E n => ψs i z.1 z.2) := (hψs i).continuous
        fun_prop
    calc eLpNorm (∑ i, carlesonSjolinOp (ψs i) R f) p volume
        ≤ ∑ i, eLpNorm (carlesonSjolinOp (ψs i) R f) p volume := eLpNorm_sum_le haesm hp
      _ ≤ ∑ i, (C i : ℝ≥0∞) * ENNReal.ofReal (R ^ (δ + ((n : ℝ) - 1) / 2 + 1 - n)) *
            eLpNorm f p volume := Finset.sum_le_sum (fun i _ => hC i R hR f)
      _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; push_cast; rfl
  · obtain ⟨C, hC⟩ := trivial_bound p hp hpt ψ hψ.continuous hψc
    refine ⟨C, fun R hR f => (hC R f).trans ?_⟩
    have h1 : 1 ≤ R ^ (δ + ((n : ℝ) - 1) / 2 + 1 - n) := Real.one_le_rpow hR (not_lt.1 hneg)
    have h2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (R ^ (δ + ((n : ℝ) - 1) / 2 + 1 - n)) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1
    calc (C : ℝ≥0∞) * eLpNorm f p volume = C * 1 * eLpNorm f p volume := by rw [mul_one]
      _ ≤ _ := by gcongr

end TaoBR.CS.PartMain
end

section
open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace
namespace TaoBR
namespace CS
variable {n : ℕ}
/-! ## The theorem -/
alias carlesonSjolinOp_le_of_br_dev := TaoBR.CS.PartMain.carlesonSjolinOp_le_of_br_dev

end CS
end TaoBR
end


theorem solution : type_of% @TaoBR.CS.carlesonSjolinOp_le_of_br_dev :=
  @TaoBR.CS.carlesonSjolinOp_le_of_br_dev
