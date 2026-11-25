-- Prove2me | solution 1 for ZetaZeros.D.EllReg.regularity_inductive_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:04:47.488034+00:00
-- url     : https://prove2.me/submissions/7cd0b39e-3f3c-4767-bff9-7bf687ba39c2

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_StepCore
import Theorems.Thm_ZetaZeros_D_EllReg_lintegral_weight_fourier_lt_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {d : ℕ}
private lemma jb_pos (ξ : E d) : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
private lemma om_nonneg' (s M ε : ℝ) (ξ : E d) : 0 ≤ om s M ε ξ := by
  unfold om; have := jb_pos ξ; positivity
private lemma om_meas (s M ε : ℝ) : Measurable (om (d := d) s M ε) := by unfold om; fun_prop
private lemma om_add (s t M ε : ℝ) (ξ : E d) :
    om (s + t) M ε ξ = (1 + ‖ξ‖ ^ 2) ^ (t / 2) * om s M ε ξ := by
  unfold om
  rw [add_div, Real.rpow_add (jb_pos ξ)]; ring
private lemma om_mono (s s' M ε : ℝ) (h : s ≤ s') (ξ : E d) : om s M ε ξ ≤ om s' M ε ξ := by
  unfold om
  have h1 : (1 : ℝ) ≤ 1 + ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ‖ξ‖]
  have h2 : 0 ≤ (1 + ε ^ 2 * ‖ξ‖ ^ 2) ^ (-(M / 2)) := by
    have : 0 ≤ 1 + ε ^ 2 * ‖ξ‖ ^ 2 := by positivity
    positivity
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) h2
private lemma weight_le_unshifted_weight (s M ε : ℝ) (hM : 0 ≤ M) (ξ : E d) : om s M ε ξ ≤ om s 0 0 ξ := by
  unfold om
  have h1 : (1 : ℝ) ≤ 1 + ε ^ 2 * ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ε, sq_nonneg ‖ξ‖, mul_nonneg (sq_nonneg ε) (sq_nonneg ‖ξ‖)]
  have h2 : (1 + ε ^ 2 * ‖ξ‖ ^ 2) ^ (-(M / 2)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
  have h3 : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ (s / 2) := by have := jb_pos ξ; positivity
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero, zero_div, neg_zero,
    Real.rpow_zero, mul_one]
  exact mul_le_of_le_one_right h3 h2
private lemma norm_mono_le {n : ℕ} (w : Fin n → Fin d) (ξ : E d) :
    ‖mono w ξ‖ ≤ (2 * Real.pi) ^ n * (1 + ‖ξ‖ ^ 2) ^ ((n : ℝ) / 2) := by
  unfold mono
  rw [norm_prod]
  have hj : ∀ j : Fin d, ‖(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ))‖ ≤ 2 * Real.pi * (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    intro j
    have e : ‖(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ))‖ = 2 * Real.pi * |ξ j| := by
      simp [Complex.norm_real, abs_of_pos Real.pi_pos]
    rw [e]
    have h1 : |ξ j| ≤ ‖ξ‖ := by simpa using PiLp.norm_apply_le ξ j
    have h2 : ‖ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.le_sqrt_of_sq_le (by linarith)
    have := Real.pi_pos
    nlinarith
  calc ∏ l, ‖(2 * Real.pi * Complex.I * ((ξ (w l) : ℝ) : ℂ))‖
      ≤ ∏ _l : Fin n, 2 * Real.pi * (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun l _ => hj (w l))
    _ = (2 * Real.pi) ^ n * (1 + ‖ξ‖ ^ 2) ^ ((n : ℝ) / 2) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← Real.rpow_mul_natCast (jb_pos ξ).le]
        congr 2; ring
private lemma nrm_eq_wn (s M ε : ℝ) (F : E d → ℂ) : nrm s M ε F = wn s M ε F ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := (volume : Measure (E d)))
    (f := fun ξ => om s M ε ξ * ‖F ξ‖) (p := 2) (by norm_num)
  unfold wn
  have e2 : ((2 : NNReal) : ℝ≥0∞) = 2 := rfl
  rw [e2] at h
  rw [← ENNReal.rpow_natCast, show ((2 : ℕ) : ℝ) = ((2 : NNReal) : ℝ) by norm_num, h]
  unfold nrm
  congr 1; ext ξ
  rw [Real.enorm_eq_ofReal (mul_nonneg (om_nonneg' _ _ _ _) (norm_nonneg _)),
    ENNReal.ofReal_mul (om_nonneg' _ _ _ _), ofReal_norm, show ((2 : NNReal) : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    ENNReal.rpow_natCast, mul_pow]
private lemma wn_eq_nrm (s M ε : ℝ) (F : E d → ℂ) : wn s M ε F = nrm s M ε F ^ (1 / 2 : ℝ) := by
  rw [nrm_eq_wn, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
private lemma wn_lt_top_iff (s M ε : ℝ) (F : E d → ℂ) : wn s M ε F < ⊤ ↔ nrm s M ε F < ⊤ := by
  rw [nrm_eq_wn]
  constructor
  · intro h; exact ENNReal.pow_lt_top h
  · intro h
    by_contra h'
    rw [not_lt, top_le_iff] at h'
    rw [h'] at h; simp at h
private lemma wn_le_of (s s' M M' ε ε' : ℝ) (F G : E d → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ ξ, om s M ε ξ * ‖F ξ‖ ≤ c * (om s' M' ε' ξ * ‖G ξ‖)) :
    wn s M ε F ≤ ENNReal.ofReal c * wn s' M' ε' G := by
  unfold wn
  have : eLpNorm (fun ξ => om s M ε ξ * ‖F ξ‖) 2 volume ≤
      eLpNorm (c • fun ξ => om s' M' ε' ξ * ‖G ξ‖) 2 volume := by
    apply eLpNorm_mono
    intro ξ
    simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (om_nonneg' _ _ _ _) (norm_nonneg _)),
      abs_of_nonneg (mul_nonneg hc (mul_nonneg (om_nonneg' _ _ _ _) (norm_nonneg _)))]
    exact h ξ
  rw [eLpNorm_const_smul] at this
  simpa [Real.enorm_eq_ofReal hc] using this
private lemma wn_mono_alt (s s' M ε : ℝ) (hs : s ≤ s') (F : E d → ℂ) : wn s M ε F ≤ wn s' M ε F := by
  simpa using wn_le_of s s' M M ε ε F F 1 zero_le_one
    (fun ξ => by rw [one_mul]; exact mul_le_mul_of_nonneg_right (om_mono s s' M ε hs ξ) (norm_nonneg _))
private lemma weightedNorm_le_unshifted (s M ε : ℝ) (hM : 0 ≤ M) (F : E d → ℂ) : wn s M ε F ≤ wn s 0 0 F := by
  simpa using wn_le_of s s M 0 ε 0 F F 1 zero_le_one
    (fun ξ => by rw [one_mul]; exact mul_le_mul_of_nonneg_right (weight_le_unshifted_weight s M ε hM ξ) (norm_nonneg _))
private lemma wn_mono_mul (a M ε : ℝ) {n : ℕ} (w : Fin n → Fin d) (F : E d → ℂ) :
    wn a M ε (fun ξ => mono w ξ * F ξ) ≤ ENNReal.ofReal ((2 * Real.pi) ^ n) * wn (a + n) M ε F := by
  apply wn_le_of _ _ _ _ _ _ _ _ _ (by positivity)
  intro ξ
  rw [norm_mul, om_add]
  have h := norm_mono_le w ξ
  have h0 := om_nonneg' a M ε ξ
  have h1 := norm_nonneg (F ξ)
  calc om a M ε ξ * (‖mono w ξ‖ * ‖F ξ‖) ≤ om a M ε ξ * (((2 * Real.pi) ^ n * (1 + ‖ξ‖ ^ 2) ^ ((n : ℝ) / 2)) * ‖F ξ‖) := by
        gcongr
    _ = _ := by ring
private lemma fourier_cont {f : E d → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by exact continuous_inner) hf
private lemma fourier_cont_of {f : E d → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) : Continuous (𝓕 f) :=
  fourier_cont (hf.integrable_of_hasCompactSupport hfc)
private lemma conv_meas {K F : E d → ℂ} (hK : Continuous K) (hF : Continuous F) : Measurable (conv K F) := by
  have h : StronglyMeasurable (Function.uncurry fun ξ η : E d => K (ξ - η) * F η) := by
    apply Continuous.stronglyMeasurable
    exact (hK.comp (continuous_fst.sub continuous_snd)).mul (hF.comp continuous_snd)
  exact (StronglyMeasurable.integral_prod_right (ν := (volume : Measure (E d))) h).measurable
private lemma wt_aesm (s M ε : ℝ) {G : E d → ℂ} (hG : Measurable G) :
    AEStronglyMeasurable (fun ξ => om s M ε ξ * ‖G ξ‖) volume :=
  ((om_meas s M ε).mul hG.norm).aestronglyMeasurable
private lemma conv_wn (hCB : ConvBound) (s M ε C N : ℝ) (hC : 0 ≤ C)
    (hW : ∀ ξ η : E d, |om s M ε ξ - om s M ε η| ≤ C * ‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N * om (s - 1) M ε η)
    (K F : E d → ℂ) (hK : Continuous K) (hF : Continuous F) :
    wn s M ε (conv K F) ≤ (∫⁻ ζ, ‖K ζ‖ₑ) * wn s M ε F +
      ENNReal.ofReal C * (∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖K ζ‖ₑ) * wn (s - 1) M ε F := by
  rw [wn_eq_nrm, wn_eq_nrm, wn_eq_nrm]
  exact hCB d s M ε C N hC hW K F hK hF
private lemma kern_fin {g : E d → ℂ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (N : ℝ) :
    (∫⁻ ζ, ‖𝓕 g ζ‖ₑ) < ⊤ ∧ (∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖𝓕 g ζ‖ₑ) < ⊤ := by
  constructor
  · have h := lintegral_weight_fourier_lt_top hg hgc 0
    simpa using h
  · have h := lintegral_weight_fourier_lt_top hg hgc (⌈N⌉₊ + 1)
    refine lt_of_le_of_lt (lintegral_mono fun ζ => ?_) h
    gcongr
    have t0 : (1 : ℝ) ≤ 1 + ‖ζ‖ := by linarith [norm_nonneg ζ]
    calc ‖ζ‖ * (1 + ‖ζ‖) ^ N ≤ (1 + ‖ζ‖) ^ (1 : ℝ) * (1 + ‖ζ‖) ^ N := by
          rw [Real.rpow_one]; gcongr; linarith
      _ = (1 + ‖ζ‖) ^ (N + 1) := by rw [← Real.rpow_add (by linarith)]; ring_nf
      _ ≤ (1 + ‖ζ‖) ^ ((⌈N⌉₊ + 1 : ℕ) : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le t0
          push_cast; linarith [Nat.le_ceil N]
      _ = (1 + ‖ζ‖) ^ (⌈N⌉₊ + 1) := Real.rpow_natCast _ _
private lemma mono_cont {n : ℕ} (w : Fin n → Fin d) : Continuous (mono (d := d) w) := by
  unfold mono; fun_prop
private lemma wn_congr (s M ε : ℝ) {F G : E d → ℂ} (h : ∀ ξ, ‖F ξ‖ = ‖G ξ‖) : wn s M ε F = wn s M ε G := by
  unfold wn; congr 1; ext ξ; rw [h]
private lemma term_out (hCB : ConvBound) (hWD : WeightDiff) (M : ℝ) (hM : 0 ≤ M) {g : E d → ℂ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) {F : E d → ℂ} (hF : Continuous F) (s a : ℝ) {n : ℕ}
    (w : Fin n → Fin d) (has : a + n ≤ s) (hFs : wn s 0 0 F < ⊤) :
    ∃ B < ⊤, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      wn a M ε (fun ξ => (-1 : ℂ) ^ n * mono w ξ * conv (𝓕 g) F ξ) ≤ B := by
  obtain ⟨C, N, hC, -, hW⟩ := hWD d s M hM
  obtain ⟨h1, h2⟩ := kern_fin hg hgc N
  have hK : Continuous (𝓕 g) := fourier_cont_of hg.continuous hgc
  refine ⟨ENNReal.ofReal ((2 * Real.pi) ^ n) * ((∫⁻ ζ, ‖𝓕 g ζ‖ₑ) * wn s 0 0 F +
      ENNReal.ofReal C * (∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖𝓕 g ζ‖ₑ) * wn s 0 0 F), ?_, ?_⟩
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top h1 hFs, ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2) hFs⟩)
  intro ε hε0 hε1
  have e : wn a M ε (fun ξ => (-1 : ℂ) ^ n * mono w ξ * conv (𝓕 g) F ξ) =
      wn a M ε (fun ξ => mono w ξ * conv (𝓕 g) F ξ) := wn_congr _ _ _ (fun ξ => by simp)
  rw [e]
  refine (wn_mono_mul a M ε w _).trans ?_
  gcongr
  refine (wn_mono_alt _ _ M ε has _).trans ?_
  refine (conv_wn hCB s M ε C N hC (hW ε hε0 hε1) _ _ hK hF).trans ?_
  gcongr
  · exact weightedNorm_le_unshifted s M ε hM F
  · exact (wn_mono_alt _ _ M ε (by linarith) F).trans (weightedNorm_le_unshifted s M ε hM F)
private lemma term_in (hCB : ConvBound) (hWD : WeightDiff) (M : ℝ) (hM : 0 ≤ M) {g : E d → ℂ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) {F : E d → ℂ} (hF : Continuous F) (s a : ℝ) {n : ℕ}
    (w : Fin n → Fin d) (has : a + n ≤ s) (hFs : wn s 0 0 F < ⊤) :
    ∃ B < ⊤, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      wn a M ε (conv (𝓕 g) (fun η => mono w η * F η)) ≤ B := by
  obtain ⟨C, N, hC, -, hW⟩ := hWD d a M hM
  obtain ⟨h1, h2⟩ := kern_fin hg hgc N
  have hK : Continuous (𝓕 g) := fourier_cont_of hg.continuous hgc
  set T := ENNReal.ofReal ((2 * Real.pi) ^ n) * wn s 0 0 F with hT
  have hTf : T < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFs
  refine ⟨(∫⁻ ζ, ‖𝓕 g ζ‖ₑ) * T +
      ENNReal.ofReal C * (∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖𝓕 g ζ‖ₑ) * T, ?_, ?_⟩
  · exact ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top h1 hTf, ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2) hTf⟩
  intro ε hε0 hε1
  refine (conv_wn hCB a M ε C N hC (hW ε hε0 hε1) _ _ hK ((mono_cont w).mul hF)).trans ?_
  gcongr
  · refine (wn_mono_mul a M ε w F).trans ?_
    rw [hT]
    gcongr
    exact (wn_mono_alt _ _ M ε has F).trans (weightedNorm_le_unshifted s M ε hM F)
  · refine (wn_mono_mul (a - 1) M ε w F).trans ?_
    rw [hT]
    gcongr
    exact (wn_mono_alt _ _ M ε (by linarith) F).trans (weightedNorm_le_unshifted s M ε hM F)
private lemma term_top (hCB : ConvBound) (hWD : WeightDiff) (M : ℝ) (hM : 0 ≤ M) {K : E d → ℂ}
    (hK : Continuous K) (hKm : ∀ N : ℝ, (∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖K ζ‖ₑ) < ⊤)
    {F : E d → ℂ} (hF : Continuous F) (a : ℝ) {n : ℕ} (w : Fin n → Fin d) (hFs : wn (a - 1 + n) 0 0 F < ⊤) :
    ∃ B < ⊤, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      wn a M ε (conv K (fun η => mono w η * F η)) ≤
        B + ENNReal.ofReal ((2 * Real.pi) ^ n) * (∫⁻ ζ, ‖K ζ‖ₑ) * wn (a + n) M ε F := by
  obtain ⟨C, N, hC, -, hW⟩ := hWD d a M hM
  have h2 := hKm N
  set T := ENNReal.ofReal ((2 * Real.pi) ^ n) * wn (a - 1 + n) 0 0 F with hT
  have hTf : T < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFs
  refine ⟨ENNReal.ofReal C * (∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖K ζ‖ₑ) * T, ?_, ?_⟩
  · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2) hTf
  intro ε hε0 hε1
  refine (conv_wn hCB a M ε C N hC (hW ε hε0 hε1) _ _ hK ((mono_cont w).mul hF)).trans ?_
  rw [add_comm]
  have hA : (∫⁻ ζ, ‖K ζ‖ₑ) * wn a M ε (fun η => mono w η * F η) ≤
      ENNReal.ofReal ((2 * Real.pi) ^ n) * (∫⁻ ζ, ‖K ζ‖ₑ) * wn (a + n) M ε F := by
    calc (∫⁻ ζ, ‖K ζ‖ₑ) * wn a M ε (fun η => mono w η * F η)
        ≤ (∫⁻ ζ, ‖K ζ‖ₑ) * (ENNReal.ofReal ((2 * Real.pi) ^ n) * wn (a + n) M ε F) :=
          mul_le_mul' le_rfl (wn_mono_mul a M ε w F)
      _ = _ := by ring
  have hB : ENNReal.ofReal C * (∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖K ζ‖ₑ) *
      wn (a - 1) M ε (fun η => mono w η * F η) ≤
      ENNReal.ofReal C * (∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖K ζ‖ₑ) * T := by
    refine mul_le_mul' le_rfl ?_
    refine (wn_mono_mul (a - 1) M ε w F).trans ?_
    rw [hT]
    exact mul_le_mul' le_rfl (weightedNorm_le_unshifted _ M ε hM F)
  exact add_le_add hB hA
private lemma level_i (hCB : ConvBound) (hWD : WeightDiff) (M : ℝ) (hM : 0 ≤ M) (s : ℝ) (m : ℕ)
    (A V W : E d → ℂ) (hV : Continuous V) (hW : Continuous W)
    (Kt : (Fin m → Fin d) → E d → ℂ) (hKt : ∀ w, Continuous (Kt w))
    (hKm : ∀ w, ∀ N : ℝ, (∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖Kt w ζ‖ₑ) < ⊤)
    (lo c : (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (hlo : ∀ n w, ContDiff ℝ ∞ (lo n w) ∧ HasCompactSupport (lo n w))
    (hc : ∀ n w, ContDiff ℝ ∞ (c n w) ∧ HasCompactSupport (c n w))
    (hid : ∀ ξ, A ξ * V ξ + ∑ w : Fin m → Fin d, conv (Kt w) (fun η => mono w η * V η) ξ
        + ∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, conv (𝓕 (lo n w)) (fun η => mono w η * V η) ξ
        = ∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, (-1 : ℂ) ^ n * mono w ξ * conv (𝓕 (c n w)) W ξ)
    (hVs : wn s 0 0 V < ⊤) (hWs : wn s 0 0 W < ⊤) :
    ∃ B < ⊤, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      wn (s + 1 - m) M ε (fun ξ => A ξ * V ξ) ≤
        B + (∑ w : Fin m → Fin d, ENNReal.ofReal ((2 * Real.pi) ^ m) * (∫⁻ ζ, ‖Kt w ζ‖ₑ)) * wn (s + 1) M ε V := by
  set a : ℝ := s + 1 - m with ha
  have e1 : a - 1 + m = s := by rw [ha]; ring
  have e2 : a + m = s + 1 := by rw [ha]; ring
  have Ht : ∀ w : Fin m → Fin d, ∃ B < ⊤, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      wn a M ε (conv (Kt w) (fun η => mono w η * V η)) ≤
        B + ENNReal.ofReal ((2 * Real.pi) ^ m) * (∫⁻ ζ, ‖Kt w ζ‖ₑ) * wn (s + 1) M ε V := by
    intro w
    have h := term_top hCB hWD M hM (hKt w) (hKm w) hV a w (by rw [e1]; exact hVs)
    rw [e2] at h
    exact h
  choose Bt hBt_fin hBt using Ht
  have Hl : ∀ (n : ℕ) (w : Fin n → Fin d), ∃ B < ⊤, n < m → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      wn a M ε (conv (𝓕 (lo n w)) (fun η => mono w η * V η)) ≤ B := by
    intro n w
    by_cases hn : n < m
    · obtain ⟨B, hB, h⟩ := term_in hCB hWD M hM (hlo n w).1 (hlo n w).2 hV s a w
        (by rw [ha]; have : (n : ℝ) + 1 ≤ m := by exact_mod_cast hn
            linarith) hVs
      exact ⟨B, hB, fun _ => h⟩
    · exact ⟨0, by simp, fun h => absurd h hn⟩
  choose Bl hBl_fin hBl using Hl
  have Ho : ∀ (n : ℕ) (w : Fin n → Fin d), ∃ B < ⊤, n < m → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      wn a M ε (fun ξ => (-1 : ℂ) ^ n * mono w ξ * conv (𝓕 (c n w)) W ξ) ≤ B := by
    intro n w
    by_cases hn : n < m
    · obtain ⟨B, hB, h⟩ := term_out hCB hWD M hM (hc n w).1 (hc n w).2 hW s a w
        (by rw [ha]; have : (n : ℝ) + 1 ≤ m := by exact_mod_cast hn
            linarith) hWs
      exact ⟨B, hB, fun _ => h⟩
    · exact ⟨0, by simp, fun h => absurd h hn⟩
  choose Bo hBo_fin hBo using Ho
  refine ⟨(∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, Bo n w) + (∑ w : Fin m → Fin d, Bt w) +
      (∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, Bl n w), ?_, ?_⟩
  · refine ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨?_, ?_⟩, ?_⟩
    · exact ENNReal.sum_lt_top.2 fun n _ => ENNReal.sum_lt_top.2 fun w _ => hBo_fin n w
    · exact ENNReal.sum_lt_top.2 fun w _ => hBt_fin w
    · exact ENNReal.sum_lt_top.2 fun n _ => ENNReal.sum_lt_top.2 fun w _ => hBl_fin n w
  intro ε hε0 hε1

  let Ro : (n : ℕ) → (Fin n → Fin d) → E d → ℝ := fun n w ξ =>
    om a M ε ξ * ‖(-1 : ℂ) ^ n * mono w ξ * conv (𝓕 (c n w)) W ξ‖
  let To : (Fin m → Fin d) → E d → ℝ := fun w ξ => om a M ε ξ * ‖conv (Kt w) (fun η => mono w η * V η) ξ‖
  let Lo : (n : ℕ) → (Fin n → Fin d) → E d → ℝ := fun n w ξ =>
    om a M ε ξ * ‖conv (𝓕 (lo n w)) (fun η => mono w η * V η) ξ‖
  have mRo : ∀ n w, AEStronglyMeasurable (Ro n w) volume := fun n w =>
    wt_aesm a M ε ((((continuous_const.mul (mono_cont w)).measurable).mul
      (conv_meas (fourier_cont_of (hc n w).1.continuous (hc n w).2) hW)))
  have mTo : ∀ w, AEStronglyMeasurable (To w) volume := fun w =>
    wt_aesm a M ε (conv_meas (hKt w) ((mono_cont w).mul hV))
  have mLo : ∀ n w, AEStronglyMeasurable (Lo n w) volume := fun n w =>
    wt_aesm a M ε (conv_meas (fourier_cont_of (hlo n w).1.continuous (hlo n w).2) ((mono_cont w).mul hV))
  have hpt : ∀ ξ, om a M ε ξ * ‖A ξ * V ξ‖ ≤
      ((∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, Ro n w) + (∑ w : Fin m → Fin d, To w) +
        (∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, Lo n w)) ξ := by
    intro ξ
    have hR : ((∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, Ro n w) + (∑ w : Fin m → Fin d, To w) +
        (∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, Lo n w)) ξ = om a M ε ξ *
        ((∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, ‖(-1 : ℂ) ^ n * mono w ξ * conv (𝓕 (c n w)) W ξ‖) +
         (∑ w : Fin m → Fin d, ‖conv (Kt w) (fun η => mono w η * V η) ξ‖) +
         (∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, ‖conv (𝓕 (lo n w)) (fun η => mono w η * V η) ξ‖)) := by
      simp only [Pi.add_apply, Finset.sum_apply, Ro, To, Lo, mul_add, Finset.mul_sum]
    rw [hR]
    refine mul_le_mul_of_nonneg_left ?_ (om_nonneg' a M ε ξ)
    have h := hid ξ
    have e : A ξ * V ξ = (∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, (-1 : ℂ) ^ n * mono w ξ * conv (𝓕 (c n w)) W ξ)
        - (∑ w : Fin m → Fin d, conv (Kt w) (fun η => mono w η * V η) ξ)
        - (∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, conv (𝓕 (lo n w)) (fun η => mono w η * V η) ξ) := by
      rw [← h]; ring
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => norm_sum_le _ _)
    · exact norm_sum_le _ _
    · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => norm_sum_le _ _)
  have hmono : wn a M ε (fun ξ => A ξ * V ξ) ≤ eLpNorm ((∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, Ro n w) +
      (∑ w : Fin m → Fin d, To w) + (∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, Lo n w)) 2 volume := by
    unfold wn
    apply eLpNorm_mono
    intro ξ
    have h0 : 0 ≤ om a M ε ξ * ‖A ξ * V ξ‖ := mul_nonneg (om_nonneg' _ _ _ _) (norm_nonneg _)
    rw [Real.norm_of_nonneg h0]
    exact (hpt ξ).trans (le_abs_self _)
  have sRo : ∀ n, AEStronglyMeasurable (∑ w : Fin n → Fin d, Ro n w) volume := fun n =>
    Finset.aestronglyMeasurable_sum _ fun w _ => mRo n w
  have sLo : ∀ n, AEStronglyMeasurable (∑ w : Fin n → Fin d, Lo n w) volume := fun n =>
    Finset.aestronglyMeasurable_sum _ fun w _ => mLo n w
  have s1 : AEStronglyMeasurable (∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, Ro n w) volume :=
    Finset.aestronglyMeasurable_sum _ fun n _ => sRo n
  have s2 : AEStronglyMeasurable (∑ w : Fin m → Fin d, To w) volume :=
    Finset.aestronglyMeasurable_sum _ fun w _ => mTo w
  have s3 : AEStronglyMeasurable (∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, Lo n w) volume :=
    Finset.aestronglyMeasurable_sum _ fun n _ => sLo n
  refine hmono.trans ((eLpNorm_add_le (p := 2) (s1.add s2) s3 (by norm_num)).trans ?_)
  refine (add_le_add (eLpNorm_add_le (p := 2) s1 s2 (by norm_num)) le_rfl).trans ?_
  have k1 : eLpNorm (∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, Ro n w) 2 volume ≤
      ∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, Bo n w := by
    refine (eLpNorm_sum_le (p := 2) (fun n _ => sRo n) (by norm_num)).trans (Finset.sum_le_sum fun n hn => ?_)
    refine (eLpNorm_sum_le (p := 2) (fun w _ => mRo n w) (by norm_num)).trans (Finset.sum_le_sum fun w _ => ?_)
    exact hBo n w (Finset.mem_range.1 hn) ε hε0 hε1
  have k2 : eLpNorm (∑ w : Fin m → Fin d, To w) 2 volume ≤
      ∑ w : Fin m → Fin d, (Bt w + ENNReal.ofReal ((2 * Real.pi) ^ m) * (∫⁻ ζ, ‖Kt w ζ‖ₑ) * wn (s + 1) M ε V) := by
    refine (eLpNorm_sum_le (p := 2) (fun w _ => mTo w) (by norm_num)).trans (Finset.sum_le_sum fun w _ => ?_)
    exact hBt w ε hε0 hε1
  have k3 : eLpNorm (∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, Lo n w) 2 volume ≤
      ∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, Bl n w := by
    refine (eLpNorm_sum_le (p := 2) (fun n _ => sLo n) (by norm_num)).trans (Finset.sum_le_sum fun n hn => ?_)
    refine (eLpNorm_sum_le (p := 2) (fun w _ => mLo n w) (by norm_num)).trans (Finset.sum_le_sum fun w _ => ?_)
    exact hBl n w (Finset.mem_range.1 hn) ε hε0 hε1
  refine (add_le_add (add_le_add k1 k2) k3).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_mul]
  ring
private lemma symb_ineq {ι : Type} [Fintype ι] (m : ι → ℕ) (k : ℕ) (hk : ∀ i, m i ≤ k) (c : ℝ) (hc : 0 < c)
    (ξ : E d) (hξ : 1 ≤ ‖ξ‖) (σ : ι → ℂ)
    (hS : c * ‖ξ‖ ^ (2 * k) ≤ ∑ i, ‖ξ‖ ^ (2 * (k - m i)) * ‖σ i‖ ^ 2) :
    c / 2 ^ k ≤ ∑ i, ((1 + ‖ξ‖ ^ 2) ^ m i)⁻¹ * ‖σ i‖ ^ 2 := by
  set J := 1 + ‖ξ‖ ^ 2 with hJ
  have hJ0 : 0 < J := jb_pos ξ
  have hx1 : 1 ≤ ‖ξ‖ ^ 2 := by nlinarith
  have hJ2 : J ≤ 2 * ‖ξ‖ ^ 2 := by rw [hJ]; linarith
  have hterm : ∀ i, ‖ξ‖ ^ (2 * (k - m i)) * ‖σ i‖ ^ 2 ≤ J ^ k * (((J ^ m i)⁻¹) * ‖σ i‖ ^ 2) := by
    intro i
    have h1 : ‖ξ‖ ^ (2 * (k - m i)) ≤ J ^ (k - m i) := by
      rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) (by rw [hJ]; linarith) _
    rw [pow_sub₀ J hJ0.ne' (hk i)] at h1
    calc ‖ξ‖ ^ (2 * (k - m i)) * ‖σ i‖ ^ 2 ≤ J ^ k * (J ^ m i)⁻¹ * ‖σ i‖ ^ 2 := by gcongr
      _ = _ := by ring
  have hsum : c * ‖ξ‖ ^ (2 * k) ≤ J ^ k * ∑ i, ((J ^ m i)⁻¹ * ‖σ i‖ ^ 2) := by
    rw [Finset.mul_sum]; exact hS.trans (Finset.sum_le_sum fun i _ => hterm i)
  have hJk : J ^ k ≤ 2 ^ k * ‖ξ‖ ^ (2 * k) := by
    rw [pow_mul, ← mul_pow]; exact pow_le_pow_left₀ hJ0.le hJ2 _
  have hJk0 : 0 < J ^ k := pow_pos hJ0 k
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  rw [div_le_iff₀ h2k]
  have : c * J ^ k ≤ J ^ k * ((∑ i, (J ^ m i)⁻¹ * ‖σ i‖ ^ 2) * 2 ^ k) := by
    calc c * J ^ k ≤ c * (2 ^ k * ‖ξ‖ ^ (2 * k)) := by gcongr
      _ = 2 ^ k * (c * ‖ξ‖ ^ (2 * k)) := by ring
      _ ≤ 2 ^ k * (J ^ k * ∑ i, ((J ^ m i)⁻¹ * ‖σ i‖ ^ 2)) := by gcongr
      _ = _ := by ring
  nlinarith
private lemma om_sub_nat (s M ε : ℝ) (n : ℕ) (ξ : E d) :
    om (s - n) M ε ξ = (1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ) / 2) * om s M ε ξ := by
  rw [sub_eq_add_neg, om_add, neg_div]
private lemma rpow_neg_half_sq (J : ℝ) (hJ : 0 < J) (n : ℕ) : (J ^ (-(n : ℝ) / 2)) ^ 2 = (J ^ n)⁻¹ := by
  rw [← Real.rpow_natCast (J ^ (-(n : ℝ) / 2)), ← Real.rpow_mul hJ.le]
  rw [show -(n : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(n : ℝ) by push_cast; ring, Real.rpow_neg hJ.le, Real.rpow_natCast]
private lemma ell_pt {ι : Type} [Fintype ι] (m : ι → ℕ) (k : ℕ) (c : ℝ) (hc : 0 < c)
    (σ A : ι → E d → ℂ) (hσA : ∀ i ξ, ‖σ i ξ‖ ≤ ‖A i ξ‖)
    (hS : ∀ ξ : E d, 1 ≤ ‖ξ‖ → c / 2 ^ k ≤ ∑ i, ((1 + ‖ξ‖ ^ 2) ^ m i)⁻¹ * ‖σ i ξ‖ ^ 2)
    (s M ε : ℝ) (V : E d → ℂ) (ξ : E d) :
    om (s + 1) M ε ξ * ‖V ξ‖ ≤ Real.sqrt 2 * (om s M ε ξ * ‖V ξ‖) +
      Real.sqrt (2 ^ k / c) * ∑ i, om (s + 1 - m i) M ε ξ * ‖A i ξ * V ξ‖ := by
  set J := 1 + ‖ξ‖ ^ 2 with hJ
  have hJ0 : 0 < J := jb_pos ξ
  have hO := om_nonneg' (s + 1) M ε ξ
  have hV := norm_nonneg (V ξ)
  have hY : 0 ≤ ∑ i, om (s + 1 - m i) M ε ξ * ‖A i ξ * V ξ‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (om_nonneg' _ _ _ _) (norm_nonneg _)
  rcases le_or_gt ‖ξ‖ 1 with h1 | h1
  · have e : om (s + 1) M ε ξ = J ^ ((1 : ℝ) / 2) * om s M ε ξ := om_add s 1 M ε ξ
    have hJ2 : J ^ ((1 : ℝ) / 2) ≤ Real.sqrt 2 := by
      rw [← Real.sqrt_eq_rpow]; apply Real.sqrt_le_sqrt; rw [hJ]; nlinarith [norm_nonneg ξ]
    have : om (s + 1) M ε ξ * ‖V ξ‖ ≤ Real.sqrt 2 * (om s M ε ξ * ‖V ξ‖) := by
      rw [e, mul_assoc]; gcongr
      exact mul_nonneg (om_nonneg' _ _ _ _) hV
    have h3 : 0 ≤ Real.sqrt (2 ^ k / c) * ∑ i, om (s + 1 - m i) M ε ξ * ‖A i ξ * V ξ‖ :=
      mul_nonneg (Real.sqrt_nonneg _) hY
    linarith
  · have hS' := hS ξ h1.le
    set q : ι → ℝ := fun i => J ^ (-(m i : ℝ) / 2) with hq
    have hq0 : ∀ i, 0 ≤ q i := fun i => by simp only [hq]; positivity
    have hq2 : ∀ i, q i ^ 2 = (J ^ m i)⁻¹ := fun i => rpow_neg_half_sq J hJ0 (m i)
    have hterm : ∀ i, q i * (om (s + 1) M ε ξ * ‖V ξ‖) * ‖σ i ξ‖ ≤ om (s + 1 - m i) M ε ξ * ‖A i ξ * V ξ‖ := by
      intro i
      have e : om (s + 1 - m i) M ε ξ = q i * om (s + 1) M ε ξ := om_sub_nat (s + 1) M ε (m i) ξ
      rw [e, norm_mul]
      have := hσA i ξ
      have := hq0 i
      calc q i * (om (s + 1) M ε ξ * ‖V ξ‖) * ‖σ i ξ‖ = (q i * om (s + 1) M ε ξ) * (‖σ i ξ‖ * ‖V ξ‖) := by ring
        _ ≤ (q i * om (s + 1) M ε ξ) * (‖A i ξ‖ * ‖V ξ‖) := by gcongr
    set X := om (s + 1) M ε ξ * ‖V ξ‖ with hX
    have hX0 : 0 ≤ X := mul_nonneg hO hV
    set Y := ∑ i, om (s + 1 - m i) M ε ξ * ‖A i ξ * V ξ‖ with hYd
    have hsq : X ^ 2 ≤ (2 ^ k / c) * Y ^ 2 := by
      have hK : 0 < 2 ^ k / c := by positivity
      have h1' : X ^ 2 * (c / 2 ^ k) ≤ X ^ 2 * ∑ i, ((J ^ m i)⁻¹ * ‖σ i ξ‖ ^ 2) := by gcongr
      have h2' : X ^ 2 * ∑ i, ((J ^ m i)⁻¹ * ‖σ i ξ‖ ^ 2) = ∑ i, (q i * X * ‖σ i ξ‖) ^ 2 := by
        rw [Finset.mul_sum]; congr 1; ext i; rw [← hq2 i]; ring
      have h3' : ∑ i, (q i * X * ‖σ i ξ‖) ^ 2 ≤ (∑ i, q i * X * ‖σ i ξ‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => mul_nonneg (mul_nonneg (hq0 i) hX0) (norm_nonneg _)
      have h4' : (∑ i, q i * X * ‖σ i ξ‖) ^ 2 ≤ Y ^ 2 := by
        apply pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (hq0 i) hX0) (norm_nonneg _))
        exact Finset.sum_le_sum fun i _ => hterm i
      have h5 : X ^ 2 * (c / 2 ^ k) ≤ Y ^ 2 := by linarith
      have e5 : X ^ 2 = X ^ 2 * (c / 2 ^ k) * (2 ^ k / c) := by field_simp
      rw [e5]
      calc X ^ 2 * (c / 2 ^ k) * (2 ^ k / c) ≤ Y ^ 2 * (2 ^ k / c) := by gcongr
        _ = _ := by ring
    have hXY : X ≤ Real.sqrt (2 ^ k / c) * Y := by
      have hR : 0 ≤ Real.sqrt (2 ^ k / c) * Y := mul_nonneg (Real.sqrt_nonneg _) hY
      apply (pow_le_pow_iff_left₀ hX0 hR (two_ne_zero)).1
      have e6 : (Real.sqrt (2 ^ k / c) * Y) ^ 2 = 2 ^ k / c * Y ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      rw [e6]
      exact hsq
    have : 0 ≤ Real.sqrt 2 * (om s M ε ξ * ‖V ξ‖) :=
      mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (om_nonneg' _ _ _ _) hV)
    linarith
private lemma ell_wn {ι : Type} [Fintype ι] (m : ι → ℕ) (k : ℕ) (c : ℝ) (hc : 0 < c)
    (σ A : ι → E d → ℂ) (hσA : ∀ i ξ, ‖σ i ξ‖ ≤ ‖A i ξ‖) (hA : ∀ i, Continuous (A i))
    (hS : ∀ ξ : E d, 1 ≤ ‖ξ‖ → c / 2 ^ k ≤ ∑ i, ((1 + ‖ξ‖ ^ 2) ^ m i)⁻¹ * ‖σ i ξ‖ ^ 2)
    (s M ε : ℝ) (V : E d → ℂ) (hV : Continuous V) :
    wn (s + 1) M ε V ≤ ENNReal.ofReal (Real.sqrt 2) * wn s M ε V +
      ENNReal.ofReal (Real.sqrt (2 ^ k / c)) * ∑ i, wn (s + 1 - m i) M ε (fun ξ => A i ξ * V ξ) := by
  set f0 : E d → ℝ := fun ξ => om s M ε ξ * ‖V ξ‖
  set f : ι → E d → ℝ := fun i ξ => om (s + 1 - m i) M ε ξ * ‖A i ξ * V ξ‖
  have m0 : AEStronglyMeasurable f0 volume := wt_aesm s M ε hV.measurable
  have mf : ∀ i, AEStronglyMeasurable (f i) volume := fun i => wt_aesm _ M ε ((hA i).mul hV).measurable
  have msum : AEStronglyMeasurable (∑ i, f i) volume := Finset.aestronglyMeasurable_sum _ fun i _ => mf i
  have h1 : wn (s + 1) M ε V ≤ eLpNorm (Real.sqrt 2 • f0 + Real.sqrt (2 ^ k / c) • ∑ i, f i) 2 volume := by
    unfold wn
    apply eLpNorm_mono
    intro ξ
    have h0 : 0 ≤ om (s + 1) M ε ξ * ‖V ξ‖ := mul_nonneg (om_nonneg' _ _ _ _) (norm_nonneg _)
    rw [Real.norm_of_nonneg h0]
    refine (ell_pt m k c hc σ A hσA hS s M ε V ξ).trans (le_trans (le_of_eq ?_) (le_abs_self _))
    simp [f0, f, Finset.sum_apply]
  refine h1.trans ((eLpNorm_add_le (p := 2) (m0.const_smul _) (msum.const_smul _) (by norm_num)).trans ?_)
  rw [eLpNorm_const_smul, eLpNorm_const_smul]
  refine add_le_add ?_ ?_
  · rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _)]; rfl
  · rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _)]
    exact mul_le_mul' le_rfl (eLpNorm_sum_le (p := 2) (fun i _ => mf i) (by norm_num))
private lemma absorb {X B : ℝ≥0∞} (hX : X < ⊤) (h : X ≤ B + ENNReal.ofReal (1 / 2) * X) : X ≤ 2 * B := by
  have hh : ENNReal.ofReal (1 / 2) * X + ENNReal.ofReal (1 / 2) * X = X := by
    rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
  have h1 : ENNReal.ofReal (1 / 2) * X + ENNReal.ofReal (1 / 2) * X ≤ B + ENNReal.ofReal (1 / 2) * X := by
    rw [hh]; exact h
  have h2 : ENNReal.ofReal (1 / 2) * X ≤ B :=
    (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hX.ne)).1 h1
  calc X = 2 * (ENNReal.ofReal (1 / 2) * X) := by
        rw [← mul_assoc, show (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 1 by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num)], one_mul]
    _ ≤ 2 * B := by gcongr
private lemma top_eq {m : ℕ} (a : (Fin m → Fin d) → ℂ) (ξ : E d) :
    ∑ w : Fin m → Fin d, a w * mono w ξ =
      (2 * Real.pi * Complex.I) ^ m * ∑ w : Fin m → Fin d, a w * ∏ l, ((ξ (w l) : ℝ) : ℂ) := by
  rw [Finset.mul_sum]
  congr 1; ext w
  unfold mono
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring
private lemma exists_pos_le {α : Type} [Finite α] (f : α → ℝ) (hf : ∀ a, 0 < f a) :
    ∃ ρ > 0, ∀ a, ρ ≤ f a := by
  rcases isEmpty_or_nonempty α with h | h
  · exact ⟨1, one_pos, fun a => (IsEmpty.false a).elim⟩
  · obtain ⟨a0, ha0⟩ := Finite.exists_min f
    exact ⟨f a0, hf a0, ha0⟩
end
end ZetaZeros.D.EllReg
end

set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {d : ℕ}
namespace ZetaZeros.D.EllReg
theorem _root_.solution : StepCore := by
  intro hSL hWD hCB hKS hDec hFW hEps hCC d ι _ P U u hH x0 hx0
  have hU : IsOpen U := hH.1
  have hcoef : ∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U := hH.2.1
  have hell : ∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0 := hH.2.2.1
  have hu : ContinuousOn u U := hH.2.2.2.1

  set k : ℕ := Finset.univ.sup P.ord with hkdef
  have hk : ∀ i, P.ord i ≤ k := fun i => Finset.le_sup (Finset.mem_univ i)
  obtain ⟨c, hc, hSc⟩ := hSL d ι P x0 k hk (hell x0 hx0)

  let b0 : ContDiffBump (0 : E d) := ⟨1, 3 / 2, by norm_num, by norm_num⟩
  set ψ0 : E d → ℝ := ⇑b0 with hψ0def
  have hψ0 : ContDiff ℝ ∞ ψ0 := b0.contDiff
  have hψ0c : HasCompactSupport ψ0 := b0.hasCompactSupport
  have hψ01 : ∀ y ∈ ball (0 : E d) 1, ψ0 y = 1 := fun y hy => b0.one_of_mem_closedBall (ball_subset_closedBall hy)
  have hψ0t : tsupport ψ0 = closedBall 0 (3 / 2) := b0.tsupport_eq
  have hψ0s : tsupport ψ0 ⊆ ball 0 2 := by rw [hψ0t]; exact closedBall_subset_ball (by norm_num)

  have HK := fun (i : ι) (w : Fin (P.ord i) → Fin d) =>
    hKS d U (P.a i (P.ord i) w) x0 ψ0 hU hx0 (hcoef i _ w) hψ0 hψ0c hψ0s
  choose r0 hr0 CK hr0U hKS' using HK

  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU x0 hx0
  obtain ⟨ρ, hρ, hρle⟩ := exists_pos_le (fun p : (Σ i : ι, (Fin (P.ord i) → Fin d)) => r0 p.1 p.2)
    (fun p => hr0 p.1 p.2)
  set S : ℝ := Real.sqrt (2 ^ k / c) *
    ∑ i, ∑ w : Fin (P.ord i) → Fin d, (2 * Real.pi) ^ (P.ord i) * max (CK i w) 0 with hSdef
  have hS0 : 0 ≤ S := mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun w _ => mul_nonneg (by positivity) (le_max_right _ _))
  set r : ℝ := min (min ρ (δ / 2)) (1 / (2 * (S + 1))) with hrdef
  have hr : 0 < r := lt_min (lt_min hρ (by linarith)) (by positivity)
  have hrρ : r ≤ ρ := (min_le_left _ _).trans (min_le_left _ _)
  have hrδ : r ≤ δ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hrS : S * r ≤ 1 / 2 := by
    have h1 : r ≤ 1 / (2 * (S + 1)) := min_le_right _ _
    calc S * r ≤ S * (1 / (2 * (S + 1))) := by gcongr
      _ ≤ 1 / 2 := by rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
  have hr0le : ∀ i w, r ≤ r0 i w := fun i w => hrρ.trans (hρle ⟨i, w⟩)
  have h2rU : ball x0 (2 * r) ⊆ U := (ball_subset_ball (by linarith)).trans hδU
  refine ⟨r, hr, (ball_subset_ball (by linarith)).trans hδU, ?_⟩
  intro s IH χ hχ hχc hχs

  obtain ⟨ρ', hρ'r, hρ'⟩ := exists_lt_subset_ball (isClosed_tsupport χ) hχs
  set ρ1 : ℝ := max ρ' (r / 2) with hρ1
  have hρ1r : ρ1 < r := max_lt hρ'r (by linarith)
  have hρ10 : 0 < ρ1 := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  let b1 : ContDiffBump x0 := ⟨(2 * ρ1 + r) / 3, (ρ1 + 2 * r) / 3, by linarith, by linarith⟩
  set χ' : E d → ℝ := ⇑b1 with hχ'def
  have hχ' : ContDiff ℝ ∞ χ' := b1.contDiff
  have hχ'c : HasCompactSupport χ' := b1.hasCompactSupport
  have hχ'r : tsupport χ' ⊆ ball x0 r := by
    rw [b1.tsupport_eq]; exact closedBall_subset_ball (by simp only [b1]; linarith)
  have hχ'U : tsupport χ' ⊆ U := hχ'r.trans ((ball_subset_ball (by linarith)).trans hδU)
  have hχ'1 : ∀ x ∈ tsupport χ, χ' =ᶠ[𝓝 x] fun _ => 1 := by
    intro x hx
    have hx' : x ∈ ball x0 ((2 * ρ1 + r) / 3) :=
      ball_subset_ball (show ρ' ≤ (2 * ρ1 + r) / 3 by linarith [le_max_left ρ' (r / 2)]) (hρ' hx)
    filter_upwards [isOpen_ball.mem_nhds hx'] with y hy
    exact b1.one_of_mem_closedBall (ball_subset_closedBall hy)

  have hcc := hCC d U u χ hU hu hχ hχc (hχs.trans ((ball_subset_ball (by linarith)).trans hδU))
  have hcc' := hCC d U u χ' hU hu hχ' hχ'c hχ'U
  set V : E d → ℂ := 𝓕 (cut χ u) with hVdef
  set W : E d → ℂ := 𝓕 (cut χ' u) with hWdef
  have hVc : Continuous V := fourier_cont_of hcc.1 hcc.2
  have hWc : Continuous W := fourier_cont_of hcc'.1 hcc'.2
  have hVs : wn s 0 0 V < ⊤ := (wn_lt_top_iff _ _ _ _).2 (IH χ hχ hχc hχs)
  have hWs : wn s 0 0 W < ⊤ := (wn_lt_top_iff _ _ _ _).2 (IH χ' hχ' hχ'c hχ'r)

  set M : ℝ := max 0 (s + 1 + d / 2) + 1 with hMdef
  have hM : 0 ≤ M := by positivity
  have hMs : s + 1 + d / 2 < M := by rw [hMdef]; linarith [le_max_right 0 (s + 1 + d / 2)]

  have HD := fun i => hDec d ι P U u hH x0 ψ0 r hψ0 hψ0c hψ01 hψ0s hr h2rU χ χ' hχ hχc hχs hχ' hχ'c hχ'U hχ'1 i
  choose lo cc hlo hcc2 hid using HD

  set Kt : (i : ι) → (Fin (P.ord i) → Fin d) → E d → ℂ := fun i w =>
    𝓕 (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ) * (P.a i (P.ord i) w x - P.a i (P.ord i) w x0)) with hKtdef
  have hχK : ∀ x, ψ0 (r⁻¹ • (x - x0)) ≠ 0 → x ∈ closedBall x0 (3 / 2 * r) := by
    intro x hx
    have h1 : r⁻¹ • (x - x0) ∈ closedBall (0 : E d) (3 / 2) := by
      rw [← hψ0t]; exact subset_tsupport _ hx
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)] at h1
    rw [mem_closedBall, dist_eq_norm]
    have := (inv_mul_le_iff₀ hr).1 h1
    linarith
  have hχKt : tsupport (fun x => ψ0 (r⁻¹ • (x - x0))) ⊆ closedBall x0 (3 / 2 * r) :=
    closure_minimal (fun x hx => hχK x hx) isClosed_closedBall
  have hχKc : HasCompactSupport (fun x => ψ0 (r⁻¹ • (x - x0))) :=
    (isCompact_closedBall x0 (3 / 2 * r)).of_isClosed_subset (isClosed_tsupport _) hχKt
  have hχKU : tsupport (fun x => ψ0 (r⁻¹ • (x - x0))) ⊆ U :=
    hχKt.trans ((closedBall_subset_ball (by linarith)).trans h2rU)
  have hχKd : ContDiff ℝ ∞ (fun x => ψ0 (r⁻¹ • (x - x0))) :=
    hψ0.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)
  have hKt : ∀ i w, Continuous (Kt i w) := by
    intro i w
    have h := hCC d U (fun x => P.a i (P.ord i) w x - P.a i (P.ord i) w x0) (fun x => ψ0 (r⁻¹ • (x - x0))) hU
      ((hcoef i _ w).continuousOn.sub continuousOn_const) hχKd hχKc hχKU
    exact fourier_cont_of h.1 h.2
  have hKm : ∀ i w, ∀ N : ℝ, (∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖Kt i w ζ‖ₑ) < ⊤ :=
    fun i w N => (hKS' i w r hr (hr0le i w)).2 N

  set A : ι → E d → ℂ := fun i ξ => ∑ w : Fin (P.ord i) → Fin d, P.a i (P.ord i) w x0 * mono w ξ with hAdef
  have HL := fun i => level_i hCB hWD M hM s (P.ord i) (A i) V W hVc hWc (Kt i) (hKt i) (hKm i) (lo i) (cc i)
    (hlo i) (hcc2 i) (fun ξ => hid i ξ) hVs hWs
  choose Bi hBi_fin hBi using HL

  have hA : ∀ i, Continuous (A i) := fun i =>
    continuous_finsetSum _ fun w _ => continuous_const.mul (mono_cont w)
  have hσA : ∀ i ξ, ‖P.symb i x0 ξ‖ ≤ ‖A i ξ‖ := by
    intro i ξ
    have e : A i ξ = (2 * Real.pi * Complex.I) ^ (P.ord i) * P.symb i x0 ξ := top_eq _ ξ
    rw [e, norm_mul, norm_pow]
    have h2 : (1 : ℝ) ≤ ‖(2 * Real.pi * Complex.I : ℂ)‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      norm_num; linarith [Real.pi_gt_three]
    have h3 : (1 : ℝ) ≤ ‖(2 * Real.pi * Complex.I : ℂ)‖ ^ (P.ord i) := one_le_pow₀ h2
    nlinarith [norm_nonneg (P.symb i x0 ξ)]
  have hSb : ∀ ξ : E d, 1 ≤ ‖ξ‖ → c / 2 ^ k ≤ ∑ i, ((1 + ‖ξ‖ ^ 2) ^ P.ord i)⁻¹ * ‖P.symb i x0 ξ‖ ^ 2 := by
    intro ξ hξ
    have hξ0 : ξ ≠ 0 := by intro h; rw [h, norm_zero] at hξ; linarith
    exact symb_ineq P.ord k hk c hc ξ hξ (fun i => P.symb i x0 ξ) (hSc ξ hξ0)

  set θ : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (2 ^ k / c)) *
    ∑ i, ∑ w : Fin (P.ord i) → Fin d, ENNReal.ofReal ((2 * Real.pi) ^ (P.ord i)) * (∫⁻ ζ, ‖Kt i w ζ‖ₑ) with hθdef
  have hθ : θ ≤ ENNReal.ofReal (1 / 2) := by
    have h1 : θ ≤ ENNReal.ofReal (Real.sqrt (2 ^ k / c)) *
        ∑ i, ∑ w : Fin (P.ord i) → Fin d, ENNReal.ofReal ((2 * Real.pi) ^ (P.ord i) * (max (CK i w) 0 * r)) := by
      rw [hθdef]
      gcongr with i _ w _
      rw [ENNReal.ofReal_mul (by positivity)]
      gcongr
      refine (hKS' i w r hr (hr0le i w)).1.trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hr.le
    refine h1.trans (le_of_eq_of_le ?_ (ENNReal.ofReal_le_ofReal hrS))
    have hnn : ∀ i (w : Fin (P.ord i) → Fin d), 0 ≤ (2 * Real.pi) ^ (P.ord i) * (max (CK i w) 0 * r) :=
      fun i w => mul_nonneg (by positivity) (mul_nonneg (le_max_right _ _) hr.le)
    rw [hSdef, mul_assoc, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    congr 1
    have e : (∑ i, ∑ w : Fin (P.ord i) → Fin d, (2 * Real.pi) ^ (P.ord i) * max (CK i w) 0) * r =
        ∑ i, ∑ w : Fin (P.ord i) → Fin d, (2 * Real.pi) ^ (P.ord i) * (max (CK i w) 0 * r) := by
      rw [Finset.sum_mul]; congr 1; ext i; rw [Finset.sum_mul]; congr 1; ext w; ring
    rw [e, ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun w _ => hnn i w)]
    congr 1; ext i
    rw [ENNReal.ofReal_sum_of_nonneg (fun w _ => hnn i w)]

  set B : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt 2) * wn s 0 0 V + ENNReal.ofReal (Real.sqrt (2 ^ k / c)) * ∑ i, Bi i
    with hBdef
  have hBf : B < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hVs,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 fun i _ => hBi_fin i)⟩
  have hunif : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → nrm (s + 1) M ε V ≤ (2 * B) ^ 2 := by
    intro ε hε0 hε1
    have hXf : wn (s + 1) M ε V < ⊤ := (wn_lt_top_iff _ _ _ _).2
      (by simpa [hVdef] using hFW d (cut χ u) hcc.1 hcc.2 (s + 1) M ε hε0 hMs)
    have hE := ell_wn P.ord k c hc (fun i ξ => P.symb i x0 ξ) A hσA hA hSb s M ε V hVc
    have hX : wn (s + 1) M ε V ≤ B + θ * wn (s + 1) M ε V := by
      refine hE.trans ?_
      have hsum : ∑ i, wn (s + 1 - P.ord i) M ε (fun ξ => A i ξ * V ξ) ≤
          ∑ i, Bi i + (∑ i, ∑ w : Fin (P.ord i) → Fin d,
            ENNReal.ofReal ((2 * Real.pi) ^ (P.ord i)) * (∫⁻ ζ, ‖Kt i w ζ‖ₑ)) * wn (s + 1) M ε V := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => hBi i ε hε0.le hε1
      calc ENNReal.ofReal (Real.sqrt 2) * wn s M ε V +
            ENNReal.ofReal (Real.sqrt (2 ^ k / c)) * ∑ i, wn (s + 1 - P.ord i) M ε (fun ξ => A i ξ * V ξ)
          ≤ ENNReal.ofReal (Real.sqrt 2) * wn s 0 0 V + ENNReal.ofReal (Real.sqrt (2 ^ k / c)) *
            (∑ i, Bi i + (∑ i, ∑ w : Fin (P.ord i) → Fin d,
              ENNReal.ofReal ((2 * Real.pi) ^ (P.ord i)) * (∫⁻ ζ, ‖Kt i w ζ‖ₑ)) * wn (s + 1) M ε V) :=
            add_le_add (mul_le_mul' le_rfl (weightedNorm_le_unshifted s M ε hM V)) (mul_le_mul' le_rfl hsum)
        _ = B + θ * wn (s + 1) M ε V := by rw [hBdef, hθdef, mul_add]; ring
    have hX' : wn (s + 1) M ε V ≤ B + ENNReal.ofReal (1 / 2) * wn (s + 1) M ε V :=
      hX.trans (add_le_add le_rfl (mul_le_mul' hθ le_rfl))
    rw [nrm_eq_wn]
    exact pow_le_pow_left₀ zero_le (absorb hXf hX') 2
  have hfin := hEps d (s + 1) M V ((2 * B) ^ 2) hM hVc hunif
  exact lt_of_le_of_lt hfin (ENNReal.pow_lt_top (ENNReal.mul_lt_top (by norm_num) hBf))
end ZetaZeros.D.EllReg
