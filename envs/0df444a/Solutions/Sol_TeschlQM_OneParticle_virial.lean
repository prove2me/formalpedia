-- Prove2me | solution 1 for TeschlQM.OneParticle.virial
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-07T15:03:39.702321+00:00
-- url     : https://prove2.me/submissions/c54bf397-ef83-43f3-9c1d-3432405f049e

import Mathlib
import Definitions.Def_TeschlQM_OneParticle_multiplicationOperator
import Definitions.Def_TeschlQM_OneParticle_freeHamiltonian

open MeasureTheory FourierTransform Filter Topology
open scoped InnerProductSpace ComplexConjugate ContDiff
open TeschlQM.OneParticle

namespace VirAux

variable {n : ℕ}

lemma inner_pt (a b : ℂ) : ⟪a, b⟫_ℂ = conj a * b := by simp [mul_comm]

/-- the factor `e^{ns/2}` of the unitary dilation group. -/
noncomputable def dfac (n : ℕ) (s : ℝ) : ℝ := Real.exp (n * s / 2)

lemma dfac_pos (s : ℝ) : 0 < dfac n s := Real.exp_pos _

lemma qmp (s : ℝ) :
    Measure.QuasiMeasurePreserving (fun x : EuclideanSpace ℝ (Fin n) => Real.exp s • x)
      volume volume :=
  Measure.quasiMeasurePreserving_smul volume (Real.exp_pos s).ne'

lemma memLp_comp_smul (f : L2 n) (s : ℝ) :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) => (f : EuclideanSpace ℝ (Fin n) → ℂ)
      (Real.exp s • x)) 2 volume := by
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin n) => Real.exp s • x) :=
    measurable_const_smul _
  have hmp := hm.measurePreserving (volume : Measure (EuclideanSpace ℝ (Fin n)))
  rw [Measure.map_addHaar_smul volume (Real.exp_pos s).ne'] at hmp
  exact ((Lp.memLp f).smul_measure ENNReal.ofReal_ne_top).comp_measurePreserving hmp

/-- The unitary dilation `(U f)(x) = e^{ns/2} f(e^s x)`. -/
noncomputable def dil (s : ℝ) (f : L2 n) : L2 n :=
  ((memLp_comp_smul f s).const_smul (dfac n s : ℂ)).toLp
    (fun x => (dfac n s : ℂ) • (f : EuclideanSpace ℝ (Fin n) → ℂ) (Real.exp s • x))

lemma coeFn_dil (s : ℝ) (f : L2 n) :
    (dil s f : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume]
      fun x => (dfac n s : ℂ) * (f : EuclideanSpace ℝ (Fin n) → ℂ) (Real.exp s • x) :=
  MemLp.coeFn_toLp _

lemma dil_add (s : ℝ) (f g : L2 n) : dil s (f + g) = dil s f + dil s g := by
  apply Lp.ext
  filter_upwards [coeFn_dil s (f + g), coeFn_dil s f, coeFn_dil s g,
    Lp.coeFn_add (dil s f) (dil s g), (qmp (n := n) s).ae (Lp.coeFn_add f g)]
    with x h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h2, h3, h5, Pi.add_apply]
  ring

lemma dil_smul (s : ℝ) (c : ℂ) (f : L2 n) : dil s (c • f) = c • dil s f := by
  apply Lp.ext
  filter_upwards [coeFn_dil s (c • f), coeFn_dil s f,
    Lp.coeFn_smul c (dil s f), (qmp (n := n) s).ae (Lp.coeFn_smul c f)]
    with x h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, h2, h4, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

lemma inner_dil (s : ℝ) (f g : L2 n) : ⟪dil s f, g⟫_ℂ = ⟪f, dil (-s) g⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  set h : EuclideanSpace ℝ (Fin n) → ℂ := fun y => conj ((dfac n s : ℂ) * f y) *
    g (Real.exp (-s) • y) with hh
  have e1 : ∫ x, ⟪(dil s f : EuclideanSpace ℝ (Fin n) → ℂ) x, g x⟫_ℂ =
      ∫ x, h (Real.exp s • x) := by
    apply integral_congr_ae
    filter_upwards [coeFn_dil s f] with x hx
    rw [inner_pt, hx, hh]
    simp only [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
  have e2 : ∫ x, ⟪(f : EuclideanSpace ℝ (Fin n) → ℂ) x, (dil (-s) g) x⟫_ℂ =
      ∫ y, ((Real.exp (n * s))⁻¹ : ℝ) • h y := by
    apply integral_congr_ae
    filter_upwards [coeFn_dil (-s) g] with x hx
    rw [inner_pt, hx, hh]
    simp only [dfac, map_mul, Complex.conj_ofReal, Complex.real_smul]
    have : (Real.exp (n * s))⁻¹ * Real.exp (n * s / 2) = Real.exp (n * -s / 2) := by
      rw [← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring
    rw [← this]
    push_cast
    ring
  rw [e1, e2, Measure.integral_comp_smul, integral_smul, finrank_euclideanSpace_fin,
    ← Real.exp_nat_mul, abs_of_pos (by positivity)]

lemma dil_neg_dil (s : ℝ) (f : L2 n) : dil (-s) (dil s f) = f := by
  apply Lp.ext
  filter_upwards [coeFn_dil (-s) (dil s f), (qmp (n := n) (-s)).ae (coeFn_dil s f)]
    with x h1 h2
  rw [h1, h2]
  simp only [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul, dfac]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  ring_nf
  simp

lemma dil_zero (f : L2 n) : dil 0 f = f := by
  apply Lp.ext
  filter_upwards [coeFn_dil 0 f] with x h1
  rw [h1]
  simp [dfac]

lemma norm_dil (s : ℝ) (f : L2 n) : ‖dil s f‖ = ‖f‖ := by
  have h : ‖dil s f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, inner_dil, dil_neg_dil]
  have := norm_nonneg (dil s f)
  have := norm_nonneg f
  nlinarith [sq_nonneg (‖dil s f‖ - ‖f‖), sq_nonneg (‖dil s f‖ + ‖f‖)]

/-- The dilation as a continuous linear map. -/
noncomputable def dilCLM (s : ℝ) : L2 n →L[ℂ] L2 n :=
  LinearMap.mkContinuous { toFun := dil s, map_add' := dil_add s, map_smul' := dil_smul s } 1
    (fun f => by simp [norm_dil])

@[simp] lemma dilCLM_apply (s : ℝ) (f : L2 n) : dilCLM s f = dil s f := rfl

section FourierPart

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

lemma continuous_fourier_fun {G : V → ℂ} (hG : Integrable G) : Continuous (𝓕 G) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simp; exact continuous_inner) hG

lemma integral_fourier_smul_eq_fun {f g : V → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ • g ξ = ∫ x, f x • 𝓕 g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar)
    (μ := volume) (ν := volume) (L := innerₗ V) Real.continuous_fourierChar
    (by simp; exact continuous_inner) hf hg
  have hflip : (innerₗ V).flip = innerₗ V := by
    ext x y
    simp
  rw [hflip] at h
  exact h

/-- For an integrable `L²` function, the `L²` Fourier transform is the Fourier integral. -/
lemma fourier_L2_ae_eq (g : Lp ℂ 2 (volume : Measure V)) (hg : Integrable (g : V → ℂ)) :
    ((𝓕 g : Lp ℂ 2 (volume : Measure V)) : V → ℂ) =ᵐ[volume] 𝓕 (g : V → ℂ) := by
  have hc := continuous_fourier_fun hg
  have hA : LocallyIntegrable (((𝓕 g : Lp ℂ 2 (volume : Measure V)) : V → ℂ)) volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hli : LocallyIntegrable (fun x => ((𝓕 g : Lp ℂ 2 (volume : Measure V)) : V → ℂ) x -
      𝓕 (g : V → ℂ) x) volume := hA.sub hc.locallyIntegrable
  have key := ae_eq_zero_of_integral_contDiff_smul_eq_zero hli ?_
  · filter_upwards [key] with x hx using sub_eq_zero.mp hx
  intro φ hφs hφc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := Complex.ofRealCLM.contDiff.comp hφs
  set ψ := hg₁.toSchwartzMap hg₂ with hψdef
  have hψ : ∀ x, ψ x = (φ x : ℂ) := fun x => by simp [ψ]
  have e1 : ∫ x, φ x • ((𝓕 g : Lp ℂ 2 (volume : Measure V)) : V → ℂ) x =
      ∫ ξ, (𝓕 (ψ : V → ℂ)) ξ • g ξ := by
    have := Lp.toTemperedDistribution_apply (𝓕 g) ψ
    rw [← Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.fourier_apply,
      Lp.toTemperedDistribution_apply, SchwartzMap.fourier_coe] at this
    rw [this]
    simp [hψ, Complex.real_smul]
  have e2 : ∫ x, φ x • 𝓕 (g : V → ℂ) x = ∫ ξ, (𝓕 (ψ : V → ℂ)) ξ • g ξ := by
    rw [integral_fourier_smul_eq_fun ψ.integrable hg]
    simp [hψ, Complex.real_smul]
  have i1 : Integrable (fun x => φ x • ((𝓕 g : Lp ℂ 2 (volume : Measure V)) : V → ℂ) x) :=
    hA.integrable_smul_left_of_hasCompactSupport hφs.continuous hφc
  have i2 : Integrable (fun x => φ x • 𝓕 (g : V → ℂ) x) :=
    hc.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφs.continuous hφc
  simp_rw [smul_sub]
  rw [integral_sub i1 i2, e1, e2, sub_self]

end FourierPart

lemma fourier_const_mul (c : ℂ) (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (ξ : EuclideanSpace ℝ (Fin n)) : 𝓕 (fun x => c * g x) ξ = c * 𝓕 g ξ := by
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_const_mul]
  congr 1
  ext x
  simp only [Circle.smul_def, smul_eq_mul]
  ring

lemma fourier_comp_smul (φ : EuclideanSpace ℝ (Fin n) → ℂ) {c : ℝ} (hc : c ≠ 0)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    𝓕 (fun x => φ (c • x)) ξ = |(c ^ n)⁻¹| • 𝓕 φ (c⁻¹ • ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have := Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (fun y => Real.fourierChar (-⟪c⁻¹ • y, ξ⟫_ℝ) • φ y) c
  simp only [inv_smul_smul₀ hc] at this
  rw [this, finrank_euclideanSpace_fin]
  congr 2
  ext y
  rw [real_inner_smul_left, real_inner_smul_right]

lemma fourier_dil (s : ℝ) (f : L2 n) : 𝓕 (dil s f) = dil (-s) (𝓕 f) := by
  have hT1 : Continuous (fun f : L2 n => 𝓕 (dil s f)) :=
    (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) ℂ).continuous.comp (dilCLM s).continuous
  have hT2 : Continuous (fun f : L2 n => dil (-s) (𝓕 f)) :=
    (dilCLM (-s)).continuous.comp (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) ℂ).continuous
  have hd := SchwartzMap.denseRange_toLpCLM (E := EuclideanSpace ℝ (Fin n)) (F := ℂ) (p := 2)
    (μ := volume) ENNReal.ofNat_ne_top
  have := hd.equalizer hT1 hT2 ?_
  · exact congrFun this f
  ext1 φ
  simp only [Function.comp_apply, SchwartzMap.toLpCLM_apply]
  set φL : L2 n := φ.toLp 2 volume
  have hφL := SchwartzMap.coeFn_toLp φ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))
  have hint : Integrable ((dil s φL : L2 n) : EuclideanSpace ℝ (Fin n) → ℂ) := by
    have h1 : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        (dfac n s : ℂ) * φ (Real.exp s • x)) :=
      (φ.integrable.comp_smul (Real.exp_pos s).ne').const_mul _
    refine h1.congr ?_
    filter_upwards [coeFn_dil s φL, (qmp (n := n) s).ae hφL] with x h2 h3
    rw [h2, h3]
  apply Lp.ext
  rw [SchwartzMap.toLp_fourier_eq]
  filter_upwards [fourier_L2_ae_eq _ hint, coeFn_dil (-s) ((𝓕 φ).toLp 2 volume),
    (qmp (n := n) (-s)).ae (SchwartzMap.coeFn_toLp (𝓕 φ) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))] with ξ h1 h2 h3
  rw [h1, h2, h3]
  have hcongr : 𝓕 ((dil s φL : L2 n) : EuclideanSpace ℝ (Fin n) → ℂ) ξ =
      𝓕 (fun x : EuclideanSpace ℝ (Fin n) => (dfac n s : ℂ) * φ (Real.exp s • x)) ξ := by
    apply Real.fourier_congr_ae
    filter_upwards [coeFn_dil s φL, (qmp (n := n) s).ae hφL] with x h2 h3
    rw [h2, h3]
  rw [hcongr]
  rw [fourier_const_mul, fourier_comp_smul _ (Real.exp_pos s).ne', SchwartzMap.fourier_coe,
    ← Real.exp_neg, ← Real.exp_nat_mul, abs_of_pos (by positivity)]
  simp only [dfac, Complex.real_smul]
  rw [← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  rw [← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

lemma tendsto_inner_dil_cpt (φ : L2 n) {g : EuclideanSpace ℝ (Fin n) → ℂ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) (hg2 : MemLp g 2 volume) :
    Tendsto (fun s => ⟪φ, dil s (hg2.toLp g)⟫_ℂ) (𝓝 0) (𝓝 ⟪φ, hg2.toLp g⟫_ℂ) := by
  obtain ⟨M, hM⟩ := hgs.exists_bound_of_continuous hgc
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hgs.isCompact.isBounded
  set gL := hg2.toLp g
  have hgL := hg2.coeFn_toLp
  have hF : ∀ s, ⟪φ, dil s gL⟫_ℂ =
      ∫ x, conj ((φ : EuclideanSpace ℝ (Fin n) → ℂ) x) * ((dfac n s : ℂ) * g (Real.exp s • x)) := by
    intro s
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_dil s gL, (qmp (n := n) s).ae hgL] with x h1 h2
    rw [inner_pt, h1, h2]
  have h0 : ⟪φ, gL⟫_ℂ = ∫ x, conj ((φ : EuclideanSpace ℝ (Fin n) → ℂ) x) * g x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hgL] with x h
    rw [inner_pt, h]
  simp_rw [hF]
  rw [h0]
  set K := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R * Real.exp 1) with hK
  set C := Real.exp (n / 2) * M with hC
  have hφm : AEStronglyMeasurable (fun x => conj ((φ : EuclideanSpace ℝ (Fin n) → ℂ) x)) volume :=
    Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable φ)
  apply tendsto_integral_filter_of_dominated_convergence
    (K.indicator (fun x => C * ‖(φ : EuclideanSpace ℝ (Fin n) → ℂ) x‖))
  · refine Filter.Eventually.of_forall fun s => hφm.mul ?_
    exact (continuous_const.mul (hgc.comp (continuous_const_smul _))).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) one_pos] with s hs
    refine Filter.Eventually.of_forall fun x => ?_
    have hind : 0 ≤ K.indicator (fun x => C * ‖(φ : EuclideanSpace ℝ (Fin n) → ℂ) x‖) x := by
      apply Set.indicator_nonneg
      intro y _
      have : 0 ≤ M := (norm_nonneg _).trans (hM 0)
      positivity
    by_cases hx : g (Real.exp s • x) = 0
    · simpa [hx] using hind
    · have hmem : Real.exp s • x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R :=
        hR (subset_tsupport _ hx)
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos s)] at hmem
      have hxK : x ∈ K := by
        rw [hK, Metric.mem_closedBall, dist_zero_right]
        have h1 : Real.exp (-1) ≤ Real.exp s := Real.exp_le_exp.mpr hs.1.le
        have h2 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
        have h3 : ‖x‖ * Real.exp (-1) ≤ R := by
          nlinarith [mul_le_mul_of_nonneg_left h1 (norm_nonneg x)]
        calc ‖x‖ = ‖x‖ * Real.exp (-1) * Real.exp 1 := by rw [mul_assoc, h2, mul_one]
          _ ≤ R * Real.exp 1 := mul_le_mul_of_nonneg_right h3 (Real.exp_pos 1).le
      rw [Set.indicator_of_mem hxK, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (dfac_pos s)]
      have hd : dfac n s ≤ Real.exp (n / 2) := by
        unfold dfac
        apply Real.exp_le_exp.mpr
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith [hs.2]
      have := hM (Real.exp s • x)
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
      calc ‖(φ : EuclideanSpace ℝ (Fin n) → ℂ) x‖ * (dfac n s * ‖g (Real.exp s • x)‖)
          ≤ ‖(φ : EuclideanSpace ℝ (Fin n) → ℂ) x‖ * (Real.exp (n / 2) * M) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            exact mul_le_mul hd this (norm_nonneg _) (Real.exp_pos _).le
        _ = C * ‖(φ : EuclideanSpace ℝ (Fin n) → ℂ) x‖ := by rw [hC]; ring
  · refine IntegrableOn.integrable_indicator ?_ measurableSet_closedBall
    exact (((Lp.memLp φ).locallyIntegrable (by norm_num)).integrableOn_isCompact
      (isCompact_closedBall _ _)).norm.const_mul C
  · refine Filter.Eventually.of_forall fun x => ?_
    have hc : Continuous (fun s : ℝ => conj ((φ : EuclideanSpace ℝ (Fin n) → ℂ) x) *
        ((dfac n s : ℂ) * g (Real.exp s • x))) := by
      unfold dfac
      fun_prop
    have := hc.tendsto 0
    simpa [dfac] using this

lemma tendsto_inner_dil (φ ψ : L2 n) :
    Tendsto (fun s => ⟪φ, dil s ψ⟫_ℂ) (𝓝 0) (𝓝 ⟪φ, ψ⟫_ℂ) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ := ε / (3 * (‖φ‖ + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨g, hgs, hgn, hgc, hg2⟩ := (Lp.memLp ψ).exists_hasCompactSupport_eLpNorm_sub_le
    (p := 2) ENNReal.ofNat_ne_top (ε := ENNReal.ofReal δ) (by simpa using hδ)
  set gL := hg2.toLp g
  have hψg : ‖ψ - gL‖ ≤ δ := by
    rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_sub ψ gL)]
    have : eLpNorm (⇑ψ - ⇑gL) 2 volume = eLpNorm (⇑ψ - g) 2 volume :=
      eLpNorm_congr_ae ((ae_eq_refl _).sub hg2.coeFn_toLp)
    rw [this]
    exact ENNReal.toReal_le_of_le_ofReal hδ.le hgn
  have hlim := tendsto_inner_dil_cpt φ hgc hgs hg2
  rw [Metric.tendsto_nhds] at hlim
  filter_upwards [hlim (ε / 3) (by positivity)] with s hs
  rw [dist_eq_norm] at hs ⊢
  have hsub : dil s (ψ - gL) = dil s ψ - dil s gL := by
    simpa using map_sub (dilCLM (n := n) s) ψ gL
  have e1 : ⟪φ, dil s ψ⟫_ℂ - ⟪φ, ψ⟫_ℂ = ⟪φ, dil s (ψ - gL)⟫_ℂ +
      (⟪φ, dil s gL⟫_ℂ - ⟪φ, gL⟫_ℂ) + ⟪φ, gL - ψ⟫_ℂ := by
    rw [hsub, inner_sub_right, inner_sub_right]
    ring
  rw [e1]
  have b1 : ‖⟪φ, dil s (ψ - gL)⟫_ℂ‖ ≤ ‖φ‖ * δ := (norm_inner_le_norm _ _).trans
    (by rw [norm_dil]; exact mul_le_mul_of_nonneg_left hψg (norm_nonneg _))
  have b3 : ‖⟪φ, gL - ψ⟫_ℂ‖ ≤ ‖φ‖ * δ := (norm_inner_le_norm _ _).trans
    (by rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_left hψg (norm_nonneg _))
  have hφδ : ‖φ‖ * δ ≤ ε / 3 := by
    rw [hδdef, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [norm_nonneg φ]
  calc _ ≤ ‖⟪φ, dil s (ψ - gL)⟫_ℂ‖ + ‖⟪φ, dil s gL⟫_ℂ - ⟪φ, gL⟫_ℂ‖ + ‖⟪φ, gL - ψ⟫_ℂ‖ :=
        norm_add₃_le
    _ < ε := by linarith

lemma laplaceSymbol_smul (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    laplaceSymbol n (Real.exp s • x) = (Real.exp (2 * s) : ℂ) * laplaceSymbol n x := by
  unfold laplaceSymbol
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos s),
    show Real.exp (2 * s) = Real.exp s ^ 2 by rw [← Real.exp_nat_mul]; norm_num]
  push_cast
  ring

lemma A_core (G : L2 n) (hS : MemLp (fun ξ => laplaceSymbol n ξ * G ξ) 2 volume) (s : ℝ) :
    ⟪dil s (hS.toLp _), G⟫_ℂ = (Real.exp (2 * s) : ℂ) * ⟪dil s G, hS.toLp _⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [coeFn_dil s (hS.toLp _), coeFn_dil s G, hS.coeFn_toLp,
    (qmp (n := n) s).ae hS.coeFn_toLp] with x h1 h2 h3 h4
  rw [inner_pt, inner_pt, h1, h2, h3, h4, laplaceSymbol_smul]
  simp only [laplaceSymbol, map_mul, Complex.conj_ofReal]
  ring

lemma B_core (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (hV : ∀ s : ℝ, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      V (Real.exp s • x) = Real.exp (-s) * V x)
    (ψ : L2 n) (hW : MemLp (fun x => (V x : ℂ) * ψ x) 2 volume) (s : ℝ) :
    ⟪ψ, dil s (hW.toLp _)⟫_ℂ = (Real.exp (-s) : ℂ) * ⟪hW.toLp _, dil s ψ⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [coeFn_dil s (hW.toLp _), coeFn_dil s ψ, hW.coeFn_toLp,
    (qmp (n := n) s).ae hW.coeFn_toLp, hV s] with x h1 h2 h3 h4 h5
  rw [inner_pt, inner_pt, h1, h2, h3, h4, h5]
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  ring

lemma inner_S_real (G : L2 n) (hS : MemLp (fun ξ => laplaceSymbol n ξ * G ξ) 2 volume) :
    ⟪G, hS.toLp _⟫_ℂ = ((∫ ξ, (2 * Real.pi * ‖ξ‖) ^ 2 * ‖G ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [L2.inner_def, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [hS.coeFn_toLp] with x h
  rw [inner_pt, h]
  unfold laplaceSymbol
  rw [mul_left_comm, Complex.conj_mul']
  push_cast
  ring

lemma inner_W_real (V : EuclideanSpace ℝ (Fin n) → ℝ) (ψ : L2 n)
    (hW : MemLp (fun x => (V x : ℂ) * ψ x) 2 volume) :
    ⟪ψ, hW.toLp _⟫_ℂ = ((∫ x, V x * ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
  rw [L2.inner_def, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [hW.coeFn_toLp] with x h
  rw [inner_pt, h, mul_left_comm, Complex.conj_mul']
  push_cast
  ring

lemma hasDerivAt_exp_mul (c : ℝ) : HasDerivAt (fun s : ℝ => Real.exp (c * s)) c 0 := by
  have := ((hasDerivAt_id (0 : ℝ)).const_mul c).exp
  simpa using this

lemma tendsto_slope_exp (c : ℝ) :
    Tendsto (fun s : ℝ => (((Real.exp (c * s) - 1) / s : ℝ) : ℂ)) (𝓝[≠] 0) (𝓝 (c : ℂ)) := by
  have h := (hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_exp_mul c))
  have h2 := (Complex.continuous_ofReal.tendsto (c : ℝ)).comp h
  refine h2.congr' ?_
  filter_upwards with s
  simp only [Function.comp_apply, slope_def_field, mul_zero, Real.exp_zero, sub_zero]

end VirAux

open VirAux in
theorem solution (n : ℕ) (hn : 1 ≤ n) (V : EuclideanSpace ℝ (Fin n) → ℝ) (_hVm : Measurable V)
    (hV : ∀ s : ℝ, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      V (Real.exp s • x) = Real.exp (-s) * V x)
    (lam : ℂ) (ψ : L2 n) (hψH₀ : ψ ∈ (freeHamiltonian n).domain)
    (hψV : ψ ∈ (multOp (fun x => (V x : ℂ))).domain) (hψ1 : ‖ψ‖ = 1)
    (heig : freeHamiltonian n ⟨ψ, hψH₀⟩ + multOp (fun x => (V x : ℂ)) ⟨ψ, hψV⟩ = lam • ψ) :
    lam = -⟪ψ, (freeHamiltonian n ⟨ψ, hψH₀⟩)⟫_ℂ ∧
      lam = (1 / 2 : ℂ) * ⟪ψ, (multOp (fun x => (V x : ℂ)) ⟨ψ, hψV⟩)⟫_ℂ ∧
      lam.im = 0 ∧ lam.re < 0 := by
  set G : L2 n := fourierL2 n ψ with hGdef
  have hS : MemLp (fun ξ => laplaceSymbol n ξ * G ξ) 2 volume := hψH₀
  have hW : MemLp (fun x => (V x : ℂ) * ψ x) 2 volume := hψV
  set S : L2 n := hS.toLp _ with hSdef
  set W : L2 n := hW.toLp _ with hWdef
  have hH : freeHamiltonian n ⟨ψ, hψH₀⟩ = (fourierL2 n).symm S := rfl
  have hWeq : multOp (fun x => (V x : ℂ)) ⟨ψ, hψV⟩ = W := rfl
  rw [hH, hWeq] at heig ⊢
  set H := (fourierL2 n).symm S with hHdef
  have hFH : ∀ φ : L2 n, ⟪φ, H⟫_ℂ = ⟪𝓕 φ, S⟫_ℂ := fun φ => by
    rw [hHdef, ← LinearIsometryEquiv.inner_map_map (fourierL2 n),
      LinearIsometryEquiv.apply_symm_apply]
    rfl
  have hFH' : ∀ φ : L2 n, ⟪H, φ⟫_ℂ = ⟪S, 𝓕 φ⟫_ℂ := fun φ => by
    rw [hHdef, ← LinearIsometryEquiv.inner_map_map (fourierL2 n),
      LinearIsometryEquiv.apply_symm_apply]
    rfl
  have hGF : 𝓕 ψ = G := rfl
  set a : ℝ := ∫ ξ, (2 * Real.pi * ‖ξ‖) ^ 2 * ‖(G : EuclideanSpace ℝ (Fin n) → ℂ) ξ‖ ^ 2
    with ha
  set b : ℝ := ∫ x, V x * ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ^ 2 with hb
  have hψH : ⟪ψ, H⟫_ℂ = a := by rw [hFH, hGF]; exact inner_S_real G hS
  have hψW : ⟪ψ, W⟫_ℂ = b := inner_W_real V ψ hW
  have hHψ : ⟪H, ψ⟫_ℂ = a := by rw [← inner_conj_symm, hψH, Complex.conj_ofReal]
  have hWψ : ⟪W, ψ⟫_ℂ = b := by rw [← inner_conj_symm, hψW, Complex.conj_ofReal]
  have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ1]; simp
  have hlam : lam = ((a + b : ℝ) : ℂ) := by
    have := congrArg (fun z => ⟪ψ, z⟫_ℂ) heig
    simp only [inner_add_right, inner_smul_right, hψψ, mul_one, hψH, hψW] at this
    rw [← this]
    push_cast
    ring
  have hlamc : (starRingEnd ℂ) lam = lam := by rw [hlam, Complex.conj_ofReal]
  have key : ∀ s : ℝ, ((Real.exp (-2 * s) : ℝ) - 1 : ℂ) * ⟪H, dil s ψ⟫_ℂ +
      ((Real.exp (-s) : ℝ) - 1 : ℂ) * ⟪W, dil s ψ⟫_ℂ = 0 := by
    intro s
    have e1 := congrArg (fun z => ⟪dil (-s) ψ, z⟫_ℂ) heig
    have e2 := congrArg (fun z => ⟪z, dil s ψ⟫_ℂ) heig
    simp only [inner_add_right, inner_add_left, inner_smul_right, inner_smul_left, hlamc] at e1 e2
    have hA : ⟪dil (-s) ψ, H⟫_ℂ = (Real.exp (-2 * s) : ℂ) * ⟪H, dil s ψ⟫_ℂ := by
      rw [hFH, fourier_dil, neg_neg, hGF, hFH', fourier_dil, hGF, ← inner_dil, A_core G hS s,
        ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
        show -2 * s + 2 * s = 0 by ring, Real.exp_zero]
      simp only [Complex.ofReal_one, one_mul, hSdef]
    have hB : ⟪dil (-s) ψ, W⟫_ℂ = (Real.exp (-s) : ℂ) * ⟪W, dil s ψ⟫_ℂ := by
      rw [inner_dil, neg_neg, B_core V hV ψ hW s]
    have hC : ⟪dil (-s) ψ, ψ⟫_ℂ = ⟪ψ, dil s ψ⟫_ℂ := by rw [inner_dil, neg_neg]
    rw [hA, hB, hC] at e1
    linear_combination e1 - e2
  have hAlim : Tendsto (fun s => ⟪H, dil s ψ⟫_ℂ) (𝓝[≠] 0) (𝓝 (a : ℂ)) := by
    have := tendsto_inner_dil H ψ
    rw [hHψ] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hBlim : Tendsto (fun s => ⟪W, dil s ψ⟫_ℂ) (𝓝[≠] 0) (𝓝 (b : ℂ)) := by
    have := tendsto_inner_dil W ψ
    rw [hWψ] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim := ((tendsto_slope_exp (-2)).mul hAlim).add ((tendsto_slope_exp (-1)).mul hBlim)
  have hzero : ((-2 : ℝ) : ℂ) * (a : ℂ) + ((-1 : ℝ) : ℂ) * (b : ℂ) = 0 := by
    refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs
    rw [neg_one_mul, Complex.ofReal_div, Complex.ofReal_div, Complex.ofReal_sub,
      Complex.ofReal_sub, Complex.ofReal_one, div_mul_eq_mul_div, div_mul_eq_mul_div,
      ← add_div, eq_div_iff hs0]
    linear_combination (-1 : ℂ) * key s
  have hab : b = -2 * a := by
    have : ((-2 * a + -1 * b : ℝ) : ℂ) = 0 := by push_cast at hzero ⊢; exact hzero
    have := Complex.ofReal_eq_zero.mp this
    linarith
  have ha0 : 0 ≤ a := integral_nonneg (fun ξ => by positivity)
  have ha_ne : a ≠ 0 := by
    intro h0
    have hint : Integrable (fun ξ : EuclideanSpace ℝ (Fin n) =>
        (2 * Real.pi * ‖ξ‖) ^ 2 * ‖(G : EuclideanSpace ℝ (Fin n) → ℂ) ξ‖ ^ 2) := by
      refine ((L2.integrable_inner (𝕜 := ℂ) G S).re).congr ?_
      filter_upwards [hS.coeFn_toLp] with x h
      rw [inner_pt, h]
      unfold laplaceSymbol
      rw [mul_left_comm, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
        RCLike.re_to_complex, Complex.ofReal_re]
    have hz := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun ξ => by positivity) hint).mp h0
    have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
    have h0null : ∀ᵐ ξ ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ξ ≠ 0 := by
      rw [ae_iff]
      simp [measure_singleton]
    have hG0 : G = 0 := by
      rw [Lp.eq_zero_iff_ae_eq_zero]
      filter_upwards [hz, h0null] with ξ h1 h2
      simp only [Pi.zero_apply] at h1 ⊢
      rcases mul_eq_zero.mp h1 with h | h
      · exfalso
        have : 2 * Real.pi * ‖ξ‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
        rcases mul_eq_zero.mp this with h' | h'
        · have := Real.pi_pos
          linarith
        · exact h2 (norm_eq_zero.mp h')
      · exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)
    have hψ0 : ψ = 0 := (fourierL2 n).map_eq_zero_iff.mp hG0
    rw [hψ0, norm_zero] at hψ1
    exact zero_ne_one hψ1
  have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha_ne)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hψH, hlam, hab]
    push_cast
    ring
  · rw [hψW, hlam, hab]
    push_cast
    ring
  · rw [hlam, Complex.ofReal_im]
  · rw [hlam, Complex.ofReal_re]
    linarith
