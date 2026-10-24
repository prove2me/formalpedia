-- Prove2me | solution 1 for SampleDrivenOS.Structure.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T23:28:10.037981+00:00
-- url     : https://prove2.me/submissions/966ca8a9-2964-4d16-abc9-3239c1535b12

import Mathlib
import Definitions.Def_SampleDrivenOS_Structure_Setting
import Theorems.Thm_SampleDrivenOS_Structure_lemma_17
import Theorems.Thm_SampleDrivenOS_Structure_lemma_18


open MeasureTheory Set Filter Topology



namespace SDOSMain
open SampleDrivenOS.Structure

noncomputable section

/-! ## Basic facts about feasible solutions -/

section basic
variable {p : ℝ} {q : ℝ → ℕ → ℝ}

lemma cumMass_le_one (hq : IsFeasible p q) {t : ℝ} (ht : t ∈ Icc p 1) : cumMass p q t ≤ 1 := by
  have := hq.2.2 t ht 1 le_rfl
  exact le_trans le_add_self this

lemma cumMass_mono (p : ℝ) (q : ℝ → ℕ → ℝ) : Monotone (cumMass p q) := by
  intro a b hab
  unfold cumMass
  exact lintegral_mono_set (Icc_subset_Icc_right hab)

lemma envelope_measurable (p : ℝ) (q : ℝ → ℕ → ℝ) : Measurable (envelope p q) := by
  unfold envelope
  have h1 : Measurable (fun t : ℝ => (cumMass p q t).toReal) :=
    ENNReal.measurable_toReal.comp (cumMass_mono p q).measurable
  exact (measurable_const.div measurable_id).mul (measurable_const.sub h1)

lemma toReal_cumMass_le_one (hq : IsFeasible p q) {t : ℝ} (ht : t ∈ Icc p 1) :
    (cumMass p q t).toReal ≤ 1 := by
  have := ENNReal.toReal_mono ENNReal.one_ne_top (cumMass_le_one hq ht)
  simpa using this

lemma envelope_nonneg (hp0 : 0 ≤ p) (hq : IsFeasible p q) {t : ℝ} (ht : t ∈ Icc p 1) :
    0 ≤ envelope p q t := by
  unfold envelope
  have h1 := toReal_cumMass_le_one hq ht
  have h2 : 0 ≤ t := le_trans hp0 ht.1
  have : 0 ≤ 1 / t := by positivity
  exact mul_nonneg this (by linarith)

lemma envelope_le (hq : IsFeasible p q) {t : ℝ} (ht : t ∈ Icc p 1) (ht0 : 0 < t) :
    envelope p q t ≤ 1 / t := by
  unfold envelope
  have h0 : 0 ≤ (cumMass p q t).toReal := ENNReal.toReal_nonneg
  have : 0 < 1 / t := by positivity
  have h1 := toReal_cumMass_le_one hq ht
  calc 1 / t * (1 - (cumMass p q t).toReal) ≤ 1 / t * 1 := by
        apply mul_le_mul_of_nonneg_left _ this.le; linarith
    _ = 1 / t := by ring

lemma q_le_envelope (hq : IsFeasible p q) {t : ℝ} (ht : t ∈ Icc p 1) (ht0 : 0 < t)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : q t ℓ ≤ envelope p q t := by
  have hf := hq.2.2 t ht ℓ hℓ
  have hqn : 0 ≤ q t ℓ := hq.1 t ht ℓ hℓ
  have hM : cumMass p q t ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (cumMass_le_one hq ht)
  have hA : ENNReal.ofReal (t * q t ℓ) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h2 := ENNReal.toReal_mono ENNReal.one_ne_top hf
  rw [ENNReal.toReal_add hA hM, ENNReal.toReal_ofReal (by positivity)] at h2
  simp only [ENNReal.toReal_one] at h2
  unfold envelope
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ht0]
  linarith

lemma integrableOn_Icc_of_bdd {f : ℝ → ℝ} {a b M : ℝ}
    (hm : AEStronglyMeasurable f (volume.restrict (Icc a b)))
    (hb : ∀ σ ∈ Icc a b, ‖f σ‖ ≤ M) : IntegrableOn f (Icc a b) := by
  refine ⟨hm, HasFiniteIntegral.restrict_of_bounded (C := M) measure_Icc_lt_top ?_⟩
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Filter.Eventually.of_forall hb

lemma hII {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (h : IntegrableOn f (Icc a b)) :
    IntervalIntegrable f volume a b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 h

/-- The cumulative mass as a series of component masses. -/
lemma cumMass_eq (hq : IsFeasible p q) {σ : ℝ} (hσ : σ ∈ Icc p 1) :
    cumMass p q σ = ∑' s : ℕ, ENNReal.ofReal (∫ τ in p..σ, q τ (s + 1)) := by
  unfold cumMass
  rw [lintegral_tsum]
  · congr 1; funext s
    have hint : IntegrableOn (fun t => q t (s + 1)) (Icc p σ) :=
      (hq.2.1 (s + 1) (by omega)).mono_set (Icc_subset_Icc_right hσ.2)
    rw [intervalIntegral.integral_of_le hσ.1, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal hint]
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall (fun t ht => hq.1 t ⟨ht.1, le_trans ht.2 hσ.2⟩ _ (by omega))
  · intro s
    have : IntegrableOn (fun t => q t (s + 1)) (Icc p σ) :=
      (hq.2.1 (s + 1) (by omega)).mono_set (Icc_subset_Icc_right hσ.2)
    exact this.aestronglyMeasurable.aemeasurable.ennreal_ofReal

lemma partial_mass_nonneg (hq : IsFeasible p q) {σ : ℝ} (hσ : σ ∈ Icc p 1) (s : ℕ) :
    0 ≤ ∫ τ in p..σ, q τ (s + 1) := by
  apply intervalIntegral.integral_nonneg hσ.1
  intro t ht
  exact hq.1 t ⟨ht.1, le_trans ht.2 hσ.2⟩ _ (by omega)

/-- Real form of the cumulative mass. -/
lemma cumMass_toReal (hq : IsFeasible p q) {σ : ℝ} (hσ : σ ∈ Icc p 1) :
    Summable (fun s : ℕ => ∫ τ in p..σ, q τ (s + 1)) ∧
    (cumMass p q σ).toReal = ∑' s : ℕ, ∫ τ in p..σ, q τ (s + 1) := by
  have h := cumMass_eq hq hσ
  have hne : ∑' s : ℕ, ENNReal.ofReal (∫ τ in p..σ, q τ (s + 1)) ≠ ⊤ := by
    rw [← h]; exact ne_top_of_le_ne_top ENNReal.one_ne_top (cumMass_le_one hq hσ)
  have hs := ENNReal.summable_toReal hne
  simp only [ENNReal.toReal_ofReal (partial_mass_nonneg hq hσ _)] at hs
  refine ⟨hs, ?_⟩
  rw [h, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  congr 1; funext s
  exact ENNReal.toReal_ofReal (partial_mass_nonneg hq hσ _)

end basic

/-! ## The masses and the function `φ` -/

/-- Mass of component `s + 1`. -/
def mu (p : ℝ) (q : ℝ → ℕ → ℝ) (s : ℕ) : ℝ := ∫ τ in p..1, q τ (s + 1)

/-- `φ(x) = Σ_s (μ_s - x)^+` (with `x` clamped at `0`). -/
def phi (μ : ℕ → ℝ) (x : ℝ) : ℝ := ∑' s, max (μ s - max x 0) 0

section phi
variable {μ : ℕ → ℝ}

lemma phi_term_nonneg (s : ℕ) (x : ℝ) : 0 ≤ max (μ s - max x 0) 0 := le_max_right _ _

lemma phi_term_le (hμ0 : ∀ s, 0 ≤ μ s) (s : ℕ) (x : ℝ) : max (μ s - max x 0) 0 ≤ μ s := by
  apply max_le _ (hμ0 s)
  have := le_max_right x 0
  linarith

lemma phi_summable (hμ0 : ∀ s, 0 ≤ μ s) (hμs : Summable μ) (x : ℝ) :
    Summable (fun s => max (μ s - max x 0) 0) :=
  Summable.of_nonneg_of_le (fun s => phi_term_nonneg s x) (fun s => phi_term_le hμ0 s x) hμs

lemma phi_nonneg (x : ℝ) : 0 ≤ phi μ x := tsum_nonneg (fun s => phi_term_nonneg s x)

lemma phi_le_sum (hμ0 : ∀ s, 0 ≤ μ s) (hμs : Summable μ) (x : ℝ) : phi μ x ≤ ∑' s, μ s :=
  Summable.tsum_le_tsum (fun s => phi_term_le hμ0 s x) (phi_summable hμ0 hμs x) hμs

lemma phi_antitone (hμ0 : ∀ s, 0 ≤ μ s) (hμs : Summable μ) : Antitone (phi μ) := by
  intro x y hxy
  apply Summable.tsum_le_tsum _ (phi_summable hμ0 hμs y) (phi_summable hμ0 hμs x)
  intro s
  apply max_le_max _ le_rfl
  have := max_le_max hxy (le_refl (0 : ℝ))
  linarith

lemma phi_continuous (hμ0 : ∀ s, 0 ≤ μ s) (hμs : Summable μ) : Continuous (phi μ) := by
  unfold phi
  apply continuous_tsum (u := μ) _ hμs
  · intro s x
    rw [Real.norm_eq_abs, abs_of_nonneg (phi_term_nonneg s x)]
    exact phi_term_le hμ0 s x
  · intro s
    fun_prop

lemma phi_lt_one (hμ0 : ∀ s, 0 ≤ μ s) (hμs : Summable μ) (hμ1 : ∑' s, μ s ≤ 1) {x : ℝ}
    (hx : 0 < x) : phi μ x < 1 := by
  by_cases h : ∃ s, 0 < μ s
  · obtain ⟨s, hs⟩ := h
    have hlt : max (μ s - max x 0) 0 < μ s := by
      apply max_lt _ hs
      rw [max_eq_left hx.le]; linarith
    have := Summable.tsum_lt_tsum (fun s => phi_term_le hμ0 s x) hlt
      (phi_summable hμ0 hμs x) hμs
    unfold phi; linarith
  · push_neg at h
    have : phi μ x = 0 := by
      unfold phi
      have : ∀ s, max (μ s - max x 0) 0 = 0 := by
        intro s
        have h1 := h s
        have h2 := hμ0 s
        have h3 : μ s = 0 := le_antisymm h1 h2
        rw [h3]; apply max_eq_right; have := le_max_right x 0; linarith
      simp [this]
    rw [this]; norm_num

end phi

/-! ## The operator and the monotone iteration -/

def Dom (p : ℝ) : Set ℝ := Icc p 1 ∩ Ioi 0

def integrand (μ : ℕ → ℝ) (B : ℝ → ℝ) (σ : ℝ) : ℝ := (1 - phi μ (B σ)) / σ

def Top (μ : ℕ → ℝ) (B : ℝ → ℝ) (τ : ℝ) : ℝ := ∫ σ in τ..1, integrand μ B σ

def Aseq (p : ℝ) (q : ℝ → ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun τ => ∫ σ in τ..1, envelope p q σ
  | n + 1 => Top (mu p q) (Aseq p q n)

def Ainf (p : ℝ) (q : ℝ → ℕ → ℝ) (τ : ℝ) : ℝ := ⨆ n, Aseq p q n τ

/-- The ceiling function `G` of the improved solution. -/
def Gs (p : ℝ) (q : ℝ → ℕ → ℝ) (σ : ℝ) : ℝ := integrand (mu p q) (Ainf p q) σ

section iter
variable {μ : ℕ → ℝ} {p : ℝ}

lemma Dom_sub {τ : ℝ} (hτ : τ ∈ Dom p) : Icc τ 1 ⊆ Dom p :=
  fun σ hσ => ⟨⟨le_trans hτ.1.1 hσ.1, hσ.2⟩, lt_of_lt_of_le hτ.2 hσ.1⟩

lemma integrand_nonneg (hμ0 : ∀ s, 0 ≤ μ s) (hμs : Summable μ) (hμ1 : ∑' s, μ s ≤ 1)
    (B : ℝ → ℝ) {σ : ℝ} (hσ : 0 < σ) : 0 ≤ integrand μ B σ := by
  unfold integrand
  have := le_trans (phi_le_sum hμ0 hμs (B σ)) hμ1
  apply div_nonneg _ hσ.le; linarith

lemma integrand_le (B : ℝ → ℝ) {σ : ℝ} (hσ : 0 < σ) : integrand μ B σ ≤ 1 / σ := by
  unfold integrand
  have := phi_nonneg (μ := μ) (B σ)
  apply div_le_div_of_nonneg_right _ hσ.le; linarith

lemma integrand_mono (hμ0 : ∀ s, 0 ≤ μ s) (hμs : Summable μ) {B B' : ℝ → ℝ} {σ : ℝ}
    (hσ : 0 < σ) (h : B σ ≤ B' σ) : integrand μ B σ ≤ integrand μ B' σ := by
  unfold integrand
  have := phi_antitone hμ0 hμs h
  apply div_le_div_of_nonneg_right _ hσ.le; linarith

lemma integrand_integrableOn (hμ0 : ∀ s, 0 ≤ μ s) (hμs : Summable μ) (hμ1 : ∑' s, μ s ≤ 1)
    {B : ℝ → ℝ} (hB : AntitoneOn B (Dom p)) {τ : ℝ} (hτ : τ ∈ Dom p) :
    IntegrableOn (integrand μ B) (Icc τ 1) := by
  have hBm : AEMeasurable B (volume.restrict (Icc τ 1)) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Icc (hB.mono (Dom_sub hτ))
  have hm : AEMeasurable (integrand μ B) (volume.restrict (Icc τ 1)) := by
    unfold integrand
    exact (aemeasurable_const.sub ((phi_continuous hμ0 hμs).measurable.comp_aemeasurable hBm)).div
      aemeasurable_id
  refine integrableOn_Icc_of_bdd (M := 1 / τ) hm.aestronglyMeasurable (fun σ hσ => ?_)
  have hσ0 : 0 < σ := lt_of_lt_of_le hτ.2 hσ.1
  rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg hμ0 hμs hμ1 B hσ0)]
  exact le_trans (integrand_le B hσ0) (one_div_le_one_div_of_le hτ.2 hσ.1)

/-- A generic integral `τ ↦ ∫_τ^1 f` of a non-negative function bounded by `1/σ`. -/
lemma tail_props {f : ℝ → ℝ} (hf0 : ∀ σ ∈ Dom p, 0 ≤ f σ) (hf1 : ∀ σ ∈ Dom p, f σ ≤ 1 / σ)
    (hfi : ∀ τ ∈ Dom p, IntegrableOn f (Icc τ 1)) :
    AntitoneOn (fun τ => ∫ σ in τ..1, f σ) (Dom p) ∧
    (∀ τ ∈ Dom p, 0 ≤ ∫ σ in τ..1, f σ) ∧
    (∀ τ ∈ Dom p, ∫ σ in τ..1, f σ ≤ 1 / τ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only
    have h1 : IntervalIntegrable f volume a b :=
      hII hab ((hfi a ha).mono_set (Icc_subset_Icc_right hb.1.2))
    have h2 : IntervalIntegrable f volume b 1 := hII hb.1.2 (hfi b hb)
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
    have : 0 ≤ ∫ σ in a..b, f σ := by
      apply intervalIntegral.integral_nonneg hab
      intro σ hσ
      exact hf0 σ (Dom_sub ha ⟨hσ.1, le_trans hσ.2 hb.1.2⟩)
    linarith
  · intro τ hτ
    apply intervalIntegral.integral_nonneg hτ.1.2
    intro σ hσ; exact hf0 σ (Dom_sub hτ hσ)
  · intro τ hτ
    have h : ∫ σ in τ..1, f σ ≤ ∫ σ in τ..1, (1 / τ) := by
      apply intervalIntegral.integral_mono_on hτ.1.2 (hII hτ.1.2 (hfi τ hτ))
        intervalIntegrable_const
      intro σ hσ
      exact le_trans (hf1 σ (Dom_sub hτ hσ)) (one_div_le_one_div_of_le hτ.2 hσ.1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    have : (1 - τ) * (1 / τ) ≤ 1 / τ := by
      have h0 : (0 : ℝ) < τ := hτ.2
      have h1 : τ * (1 / τ) = 1 := by field_simp
      nlinarith
    linarith

lemma Top_props (hμ0 : ∀ s, 0 ≤ μ s) (hμs : Summable μ) (hμ1 : ∑' s, μ s ≤ 1)
    {B : ℝ → ℝ} (hB : AntitoneOn B (Dom p)) :
    AntitoneOn (Top μ B) (Dom p) ∧ (∀ τ ∈ Dom p, 0 ≤ Top μ B τ) ∧
      (∀ τ ∈ Dom p, Top μ B τ ≤ 1 / τ) :=
  tail_props (fun σ hσ => integrand_nonneg hμ0 hμs hμ1 B hσ.2)
    (fun σ hσ => integrand_le B hσ.2) (fun τ hτ => integrand_integrableOn hμ0 hμs hμ1 hB hτ)

lemma Top_mono (hμ0 : ∀ s, 0 ≤ μ s) (hμs : Summable μ) (hμ1 : ∑' s, μ s ≤ 1)
    {B B' : ℝ → ℝ} (hB : AntitoneOn B (Dom p)) (hB' : AntitoneOn B' (Dom p))
    (h : ∀ σ ∈ Dom p, B σ ≤ B' σ) {τ : ℝ} (hτ : τ ∈ Dom p) : Top μ B τ ≤ Top μ B' τ := by
  unfold Top
  apply intervalIntegral.integral_mono_on hτ.1.2
    (hII hτ.1.2 (integrand_integrableOn hμ0 hμs hμ1 hB hτ))
    (hII hτ.1.2 (integrand_integrableOn hμ0 hμs hμ1 hB' hτ))
  intro σ hσ
  exact integrand_mono hμ0 hμs (lt_of_lt_of_le hτ.2 hσ.1) (h σ (Dom_sub hτ hσ))

end iter

end

end SDOSMain



namespace SDOSMain
open SampleDrivenOS.Structure

noncomputable section

section main
variable {p : ℝ} {q : ℝ → ℕ → ℝ}

lemma mu_nonneg (hq : IsFeasible p q) (hp1 : p < 1) (s : ℕ) : 0 ≤ mu p q s :=
  partial_mass_nonneg hq ⟨hp1.le, le_rfl⟩ s

lemma mu_summable (hq : IsFeasible p q) (hp1 : p < 1) : Summable (mu p q) :=
  (cumMass_toReal hq ⟨hp1.le, le_rfl⟩).1

lemma mu_sum_le (hq : IsFeasible p q) (hp1 : p < 1) : ∑' s, mu p q s ≤ 1 := by
  have h := (cumMass_toReal hq ⟨hp1.le, le_rfl⟩).2
  unfold mu
  rw [← h]
  exact toReal_cumMass_le_one hq ⟨hp1.le, le_rfl⟩

lemma envelope_integrableOn (hp0 : 0 ≤ p) (hq : IsFeasible p q) {τ : ℝ} (hτ : τ ∈ Dom p) :
    IntegrableOn (envelope p q) (Icc τ 1) := by
  refine integrableOn_Icc_of_bdd (M := 1 / τ) (envelope_measurable p q).aestronglyMeasurable
    (fun σ hσ => ?_)
  have hσ' := Dom_sub hτ hσ
  rw [Real.norm_eq_abs, abs_of_nonneg (envelope_nonneg hp0 hq hσ'.1)]
  exact le_trans (envelope_le hq hσ'.1 hσ'.2) (one_div_le_one_div_of_le hτ.2 hσ.1)

lemma A0_props (hp0 : 0 ≤ p) (hq : IsFeasible p q) :
    AntitoneOn (Aseq p q 0) (Dom p) ∧ (∀ τ ∈ Dom p, 0 ≤ Aseq p q 0 τ) ∧
      (∀ τ ∈ Dom p, Aseq p q 0 τ ≤ 1 / τ) :=
  tail_props (fun σ hσ => envelope_nonneg hp0 hq hσ.1) (fun σ hσ => envelope_le hq hσ.1 hσ.2)
    (fun τ hτ => envelope_integrableOn hp0 hq hτ)

lemma Aseq_props (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) (n : ℕ) :
    AntitoneOn (Aseq p q n) (Dom p) ∧ (∀ τ ∈ Dom p, 0 ≤ Aseq p q n τ) ∧
      (∀ τ ∈ Dom p, Aseq p q n τ ≤ 1 / τ) := by
  cases n with
  | zero => exact A0_props hp0 hq
  | succ n =>
    have ih := Aseq_props hp0 hp1 hq n
    exact Top_props (mu_nonneg hq hp1) (mu_summable hq hp1) (mu_sum_le hq hp1) ih.1

/-- `φ(A₀(σ)) ≤ M_q(σ)`: the starting point of the monotone iteration. -/
lemma phi_A0_le (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {σ : ℝ} (hσ : σ ∈ Dom p) :
    phi (mu p q) (Aseq p q 0 σ) ≤ (cumMass p q σ).toReal := by
  obtain ⟨hsum, heq⟩ := cumMass_toReal hq hσ.1
  rw [heq]
  have hA0 : 0 ≤ Aseq p q 0 σ := (A0_props hp0 hq).2.1 σ hσ
  unfold phi
  apply Summable.tsum_le_tsum _ (phi_summable (mu_nonneg hq hp1) (mu_summable hq hp1) _) hsum
  intro s
  rw [max_eq_left hA0]
  apply max_le _ (partial_mass_nonneg hq hσ.1 s)
  have hint : IntegrableOn (fun t => q t (s + 1)) (Icc p 1) := hq.2.1 (s + 1) (by omega)
  have h1 : IntervalIntegrable (fun t => q t (s + 1)) volume p σ :=
    hII hσ.1.1 (hint.mono_set (Icc_subset_Icc_right hσ.1.2))
  have h2 : IntervalIntegrable (fun t => q t (s + 1)) volume σ 1 :=
    hII hσ.1.2 (hint.mono_set (Icc_subset_Icc_left hσ.1.1))
  have e := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hle : ∫ t in σ..1, q t (s + 1) ≤ Aseq p q 0 σ := by
    show ∫ t in σ..1, q t (s + 1) ≤ ∫ t in σ..1, envelope p q t
    apply intervalIntegral.integral_mono_on hσ.1.2 h2
      (hII hσ.1.2 (envelope_integrableOn hp0 hq hσ))
    intro t ht
    exact q_le_envelope hq (Dom_sub hσ ht).1 (Dom_sub hσ ht).2 (by omega)
  unfold mu
  linarith

lemma Aseq_mono (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) (n : ℕ) :
    ∀ τ ∈ Dom p, Aseq p q n τ ≤ Aseq p q (n + 1) τ := by
  have hμ0 := mu_nonneg hq hp1
  have hμs := mu_summable hq hp1
  have hμ1 := mu_sum_le hq hp1
  induction n with
  | zero =>
    intro τ hτ
    show ∫ σ in τ..1, envelope p q σ ≤ Top (mu p q) (Aseq p q 0) τ
    unfold Top
    apply intervalIntegral.integral_mono_on hτ.1.2 (hII hτ.1.2 (envelope_integrableOn hp0 hq hτ))
      (hII hτ.1.2 (integrand_integrableOn hμ0 hμs hμ1 (A0_props hp0 hq).1 hτ))
    intro σ hσ
    have hσ' := Dom_sub hτ hσ
    have h := phi_A0_le hp0 hp1 hq hσ'
    unfold envelope integrand
    rw [one_div_mul_eq_div]
    apply div_le_div_of_nonneg_right _ (le_of_lt hσ'.2)
    linarith
  | succ n ih =>
    intro τ hτ
    exact Top_mono hμ0 hμs hμ1 (Aseq_props hp0 hp1 hq n).1 (Aseq_props hp0 hp1 hq (n + 1)).1
      ih hτ

lemma Aseq_monotone (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {τ : ℝ} (hτ : τ ∈ Dom p) :
    Monotone (fun n => Aseq p q n τ) :=
  monotone_nat_of_le_succ (fun n => Aseq_mono hp0 hp1 hq n τ hτ)

lemma Aseq_bdd (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {τ : ℝ} (hτ : τ ∈ Dom p) :
    BddAbove (range (fun n => Aseq p q n τ)) :=
  ⟨1 / τ, by rintro _ ⟨n, rfl⟩; exact (Aseq_props hp0 hp1 hq n).2.2 τ hτ⟩

lemma Aseq_tendsto (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {τ : ℝ} (hτ : τ ∈ Dom p) :
    Tendsto (fun n => Aseq p q n τ) atTop (𝓝 (Ainf p q τ)) :=
  tendsto_atTop_ciSup (Aseq_monotone hp0 hp1 hq hτ) (Aseq_bdd hp0 hp1 hq hτ)

lemma Aseq_le_Ainf (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {τ : ℝ} (hτ : τ ∈ Dom p)
    (n : ℕ) : Aseq p q n τ ≤ Ainf p q τ :=
  le_ciSup (Aseq_bdd hp0 hp1 hq hτ) n

lemma Ainf_props (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) :
    AntitoneOn (Ainf p q) (Dom p) ∧ (∀ τ ∈ Dom p, 0 ≤ Ainf p q τ) ∧
      (∀ τ ∈ Dom p, Ainf p q τ ≤ 1 / τ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    apply ciSup_le
    intro n
    exact le_trans ((Aseq_props hp0 hp1 hq n).1 ha hb hab) (Aseq_le_Ainf hp0 hp1 hq ha n)
  · intro τ hτ
    exact le_trans ((Aseq_props hp0 hp1 hq 0).2.1 τ hτ) (Aseq_le_Ainf hp0 hp1 hq hτ 0)
  · intro τ hτ
    exact ciSup_le (fun n => (Aseq_props hp0 hp1 hq n).2.2 τ hτ)

/-- The limit is a fixed point of the operator. -/
lemma Ainf_fixed (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {τ : ℝ} (hτ : τ ∈ Dom p) :
    Top (mu p q) (Ainf p q) τ = Ainf p q τ := by
  have hμ0 := mu_nonneg hq hp1
  have hμs := mu_summable hq hp1
  have hμ1 := mu_sum_le hq hp1
  have hlim1 : Tendsto (fun n => Top (mu p q) (Aseq p q n) τ) atTop
      (𝓝 (Top (mu p q) (Ainf p q) τ)) := by
    unfold Top
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1 / τ)
    · refine Filter.Eventually.of_forall (fun n => ?_)
      rw [uIoc_of_le hτ.1.2]
      exact ((integrand_integrableOn hμ0 hμs hμ1 (Aseq_props hp0 hp1 hq n).1 hτ).mono_set
        Ioc_subset_Icc_self).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun n => ?_)
      refine Filter.Eventually.of_forall (fun σ hσ => ?_)
      rw [uIoc_of_le hτ.1.2] at hσ
      have hσ0 : 0 < σ := lt_trans hτ.2 hσ.1
      rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg hμ0 hμs hμ1 _ hσ0)]
      exact le_trans (integrand_le _ hσ0) (one_div_le_one_div_of_le hτ.2 hσ.1.le)
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall (fun σ hσ => ?_)
      rw [uIoc_of_le hτ.1.2] at hσ
      have hσD : σ ∈ Dom p := Dom_sub hτ ⟨hσ.1.le, hσ.2⟩
      unfold integrand
      have h1 := ((phi_continuous hμ0 hμs).tendsto _).comp (Aseq_tendsto hp0 hp1 hq hσD)
      exact (tendsto_const_nhds.sub h1).div_const σ
  have hlim2 : Tendsto (fun n => Top (mu p q) (Aseq p q n) τ) atTop (𝓝 (Ainf p q τ)) :=
    (tendsto_add_atTop_iff_nat 1).2 (Aseq_tendsto hp0 hp1 hq hτ)
  exact tendsto_nhds_unique hlim1 hlim2

lemma Gs_nonneg (hp1 : p < 1) (hq : IsFeasible p q) {σ : ℝ} (hσ : 0 < σ) : 0 ≤ Gs p q σ :=
  integrand_nonneg (mu_nonneg hq hp1) (mu_summable hq hp1) (mu_sum_le hq hp1) _ hσ

lemma Gs_le {σ : ℝ} (hσ : 0 < σ) : Gs p q σ ≤ 1 / σ := integrand_le _ hσ

lemma Gs_integrableOn (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {τ : ℝ}
    (hτ : τ ∈ Dom p) : IntegrableOn (Gs p q) (Icc τ 1) :=
  integrand_integrableOn (mu_nonneg hq hp1) (mu_summable hq hp1) (mu_sum_le hq hp1)
    (Ainf_props hp0 hp1 hq).1 hτ

lemma Ainf_eq (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {τ : ℝ} (hτ : τ ∈ Dom p) :
    Ainf p q τ = ∫ σ in τ..1, Gs p q σ :=
  (Ainf_fixed hp0 hp1 hq hτ).symm

lemma Ainf_continuousOn (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {a : ℝ}
    (ha : a ∈ Dom p) : ContinuousOn (Ainf p q) (Icc a 1) := by
  have h := intervalIntegral.continuousOn_primitive_interval_left (μ := volume) (b := 1)
    (f := Gs p q) (a := a) (by rw [uIcc_of_le ha.1.2]; exact Gs_integrableOn hp0 hp1 hq ha)
  rw [uIcc_of_le ha.1.2] at h
  refine h.congr (fun τ hτ => ?_)
  exact Ainf_eq hp0 hp1 hq (Dom_sub ha hτ)

lemma Gs_continuousOn (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {a : ℝ}
    (ha : a ∈ Dom p) : ContinuousOn (Gs p q) (Icc a 1) := by
  unfold Gs integrand
  apply ContinuousOn.div
  · exact continuousOn_const.sub ((phi_continuous (mu_nonneg hq hp1) (mu_summable hq hp1)).comp_continuousOn
      (Ainf_continuousOn hp0 hp1 hq ha))
  · exact continuousOn_id
  · intro σ hσ; exact (lt_of_lt_of_le ha.2 hσ.1).ne'

/-- `σ G(σ) = 1 - φ(A(σ))`. -/
lemma Gs_mul (σ : ℝ) (hσ : 0 < σ) : σ * Gs p q σ = 1 - phi (mu p q) (Ainf p q σ) := by
  unfold Gs integrand; field_simp

/-- The new ceiling dominates the envelope of `q`. -/
lemma envelope_le_Gs (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {σ : ℝ}
    (hσ : σ ∈ Dom p) : envelope p q σ ≤ Gs p q σ := by
  have h1 := phi_A0_le hp0 hp1 hq hσ
  have h2 := phi_antitone (mu_nonneg hq hp1) (mu_summable hq hp1)
    (le_trans (Aseq_mono hp0 hp1 hq 0 σ hσ) (Aseq_le_Ainf hp0 hp1 hq hσ 1) :
      Aseq p q 0 σ ≤ Ainf p q σ)
  unfold envelope Gs integrand
  rw [one_div_mul_eq_div]
  apply div_le_div_of_nonneg_right _ (le_of_lt hσ.2)
  linarith

lemma q_le_Gs (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {σ : ℝ} (hσ : σ ∈ Dom p)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : q σ ℓ ≤ Gs p q σ :=
  le_trans (q_le_envelope hq hσ.1 hσ.2 hℓ) (envelope_le_Gs hp0 hp1 hq hσ)

/-- `A(p) ≥ μ_s` when `p > 0`. -/
lemma mu_le_Ainf_p (hp0 : 0 < p) (hp1 : p < 1) (hq : IsFeasible p q) (s : ℕ) :
    mu p q s ≤ Ainf p q p := by
  have hpD : p ∈ Dom p := ⟨⟨le_rfl, hp1.le⟩, hp0⟩
  refine le_trans ?_ (Aseq_le_Ainf hp0.le hp1 hq hpD 0)
  show ∫ τ in p..1, q τ (s + 1) ≤ ∫ σ in p..1, envelope p q σ
  apply intervalIntegral.integral_mono_on hp1.le (hII hp1.le (hq.2.1 (s + 1) (by omega)))
    (hII hp1.le (envelope_integrableOn hp0.le hq hpD))
  intro t ht
  exact q_le_envelope hq ht (lt_of_lt_of_le hp0 ht.1) (by omega)

end main

end

end SDOSMain



namespace SDOSMain
open SampleDrivenOS.Structure

noncomputable section

/-! ## Order statistics of a summable non-negative sequence -/

section ostat
variable {μ : ℕ → ℝ}

def Kset (μ : ℕ → ℝ) (c : ℝ) : Set ℕ := {s | c ≤ μ s}

def Kc (μ : ℕ → ℝ) (c : ℝ) : ℕ := (Kset μ c).ncard

/-- The `j`-th largest value of `μ` (for `j ≥ 1`). -/
def msort (μ : ℕ → ℝ) (j : ℕ) : ℝ := sSup {c : ℝ | 0 < c ∧ j ≤ Kc μ c}

lemma Kset_finite (hμs : Summable μ) {c : ℝ} (hc : 0 < c) : (Kset μ c).Finite := by
  have h := hμs.tendsto_atTop_zero
  have h2 : ∀ᶠ s in atTop, μ s < c := h.eventually_lt_const hc
  obtain ⟨N, hN⟩ := eventually_atTop.1 h2
  apply (Finset.range N).finite_toSet.subset
  intro s hs
  simp only [Finset.coe_range, mem_Iio]
  by_contra h'
  push_neg at h'
  have := hN s h'
  simp only [Kset, mem_setOf_eq] at hs
  linarith

lemma Kc_anti (hμs : Summable μ) {c c' : ℝ} (hc : 0 < c) (h : c ≤ c') : Kc μ c' ≤ Kc μ c := by
  apply Set.ncard_le_ncard _ (Kset_finite hμs hc)
  intro s hs
  simp only [Kset, mem_setOf_eq] at hs ⊢
  linarith

lemma mu_le_tsum (hμ0 : ∀ s, 0 ≤ μ s) (hμs : Summable μ) (s : ℕ) : μ s ≤ ∑' s, μ s :=
  hμs.le_tsum s (fun j _ => hμ0 j)

lemma msort_set_bdd (hμ0 : ∀ s, 0 ≤ μ s) (hμs : Summable μ) {j : ℕ} (hj : 1 ≤ j) :
    BddAbove {c : ℝ | 0 < c ∧ j ≤ Kc μ c} := by
  refine ⟨∑' s, μ s, fun c hc => ?_⟩
  have h1 : 0 < Kc μ c := lt_of_lt_of_le hj hc.2
  have hne : (Kset μ c).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    simp [Kc, h] at h1
  obtain ⟨s, hs⟩ := hne
  exact le_trans hs (mu_le_tsum hμ0 hμs s)

lemma msort_nonneg (j : ℕ) : 0 ≤ msort μ j := by
  apply Real.sSup_nonneg
  intro c hc; exact hc.1.le

/-- The supremum defining `msort` is attained. -/
lemma msort_mem (hμ0 : ∀ s, 0 ≤ μ s) (hμs : Summable μ) {j : ℕ} (hj : 1 ≤ j)
    (hne : {c : ℝ | 0 < c ∧ j ≤ Kc μ c}.Nonempty) :
    msort μ j ∈ {c : ℝ | 0 < c ∧ j ≤ Kc μ c} := by
  set S := {c : ℝ | 0 < c ∧ j ≤ Kc μ c} with hS
  have hbdd := msort_set_bdd hμ0 hμs hj
  set m := msort μ j with hm
  obtain ⟨c0, hc0⟩ := hne
  have hm0 : 0 < m := lt_of_lt_of_le hc0.1 (le_csSup hbdd hc0)
  refine ⟨hm0, ?_⟩
  by_contra hlt
  push_neg at hlt
  -- the finitely many values below `m` that exceed `m/2`
  set T : Set ℝ := insert (m / 2) (μ '' {s | s ∈ Kset μ (m / 2) ∧ μ s < m}) with hT
  have hTfin : T.Finite := by
    apply Set.Finite.insert
    apply Set.Finite.image
    exact (Kset_finite hμs (by linarith)).subset (fun s hs => hs.1)
  have hTne : T.Nonempty := ⟨m / 2, mem_insert _ _⟩
  have hTlt : ∀ t ∈ T, t < m := by
    intro t ht
    rcases ht with rfl | ⟨s, hs, rfl⟩
    · linarith
    · exact hs.2
  set m1 := sSup T with hm1
  have hm1mem : m1 ∈ T := hTne.csSup_mem hTfin
  have hm1lt : m1 < m := hTlt m1 hm1mem
  have hTle : ∀ t ∈ T, t ≤ m1 := fun t ht => le_csSup hTfin.bddAbove ht
  obtain ⟨c, hcS, hcm1⟩ := exists_lt_of_lt_csSup ⟨c0, hc0⟩ hm1lt
  have hsub : Kset μ c ⊆ Kset μ m := by
    intro s hs
    simp only [Kset, mem_setOf_eq] at hs ⊢
    by_contra hsm
    push_neg at hsm
    have hhalf : m / 2 ≤ m1 := hTle _ (mem_insert _ _)
    have hsK : s ∈ Kset μ (m / 2) := by
      simp only [Kset, mem_setOf_eq]; linarith
    have : μ s ∈ T := mem_insert_of_mem _ ⟨s, ⟨hsK, hsm⟩, rfl⟩
    have := hTle _ this
    linarith
  have hKc : Kc μ c ≤ Kc μ m := Set.ncard_le_ncard hsub (Kset_finite hμs hm0)
  have := hcS.2
  omega

/-- The defining property of the order statistic. -/
lemma msort_iff (hμ0 : ∀ s, 0 ≤ μ s) (hμs : Summable μ) {j : ℕ} (hj : 1 ≤ j) {c : ℝ}
    (hc : 0 < c) : c ≤ msort μ j ↔ j ≤ Kc μ c := by
  constructor
  · intro h
    have hne : {c : ℝ | 0 < c ∧ j ≤ Kc μ c}.Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      have : msort μ j = 0 := by unfold msort; rw [hne, Real.sSup_empty]
      linarith
    have hmem := msort_mem hμ0 hμs hj hne
    exact le_trans hmem.2 (Kc_anti hμs hc h)
  · intro h
    exact le_csSup (msort_set_bdd hμ0 hμs hj) ⟨hc, h⟩

lemma msort_anti (hμ0 : ∀ s, 0 ≤ μ s) (hμs : Summable μ) {j j' : ℕ} (hj : 1 ≤ j) (hjj : j ≤ j') :
    msort μ j' ≤ msort μ j := by
  by_cases hne : {c : ℝ | 0 < c ∧ j' ≤ Kc μ c}.Nonempty
  · apply csSup_le_csSup (msort_set_bdd hμ0 hμs hj) hne
    intro c hc; exact ⟨hc.1, le_trans hjj hc.2⟩
  · rw [not_nonempty_iff_eq_empty] at hne
    have : msort μ j' = 0 := by unfold msort; rw [hne, Real.sSup_empty]
    rw [this]; exact msort_nonneg j

lemma mu_le_msort_one (hμ0 : ∀ s, 0 ≤ μ s) (hμs : Summable μ) (s : ℕ) : μ s ≤ msort μ 1 := by
  rcases (hμ0 s).lt_or_eq with h | h
  · rw [msort_iff hμ0 hμs le_rfl h]
    have : 0 < Kc μ (μ s) := by
      apply Set.ncard_pos (Kset_finite hμs h) |>.2
      exact ⟨s, by simp [Kset]⟩
    omega
  · rw [← h]; exact msort_nonneg 1

lemma msort_le_sum (hμ0 : ∀ s, 0 ≤ μ s) (hμs : Summable μ) {j : ℕ} (hj : 1 ≤ j) :
    msort μ j ≤ ∑' s, μ s := by
  rcases (msort_nonneg (μ := μ) j).lt_or_eq with h | h
  · have := (msort_iff hμ0 hμs hj h).1 le_rfl
    have hne : (Kset μ (msort μ j)).Nonempty := by
      apply (Set.ncard_pos (Kset_finite hμs h)).1
      have h' : 0 < Kc μ (msort μ j) := by omega
      exact h'
    obtain ⟨s, hs⟩ := hne
    exact le_trans hs (mu_le_tsum hμ0 hμs s)
  · rw [← h]; exact tsum_nonneg hμ0

lemma msort_one_attained (hμ0 : ∀ s, 0 ≤ μ s) (hμs : Summable μ) (h : 0 < msort μ 1) :
    ∃ s, msort μ 1 ≤ μ s := by
  have := (msort_iff hμ0 hμs le_rfl h).1 le_rfl
  have hne : (Kset μ (msort μ 1)).Nonempty := by
    apply (Set.ncard_pos (Kset_finite hμs h)).1
    have h' : 0 < Kc μ (msort μ 1) := by omega
    exact h'
  exact hne

/-- Counting identity: the number of order statistics above `c` equals the number of
terms above `c`. -/
lemma count_eq (hμ0 : ∀ s, 0 ≤ μ s) (hμs : Summable μ) {c : ℝ} (hc : 0 ≤ c) :
    (∑' j : ℕ, if c ≤ msort μ (j + 1) then (1 : ENNReal) else 0) =
      ∑' s : ℕ, if c ≤ μ s then (1 : ENNReal) else 0 := by
  rcases hc.lt_or_eq with hc | hc
  · have hfin := Kset_finite hμs hc
    have h1 : (∑' j : ℕ, if c ≤ msort μ (j + 1) then (1 : ENNReal) else 0) = (Kc μ c : ENNReal) := by
      rw [tsum_eq_sum (s := Finset.range (Kc μ c))]
      · rw [Finset.sum_congr rfl (g := fun _ => (1 : ENNReal))]
        · simp
        · intro j hj
          rw [Finset.mem_range] at hj
          rw [if_pos ((msort_iff hμ0 hμs (by omega) hc).2 (by omega))]
      · intro j hj
        rw [Finset.mem_range] at hj
        rw [if_neg]
        rw [msort_iff hμ0 hμs (by omega) hc]; omega
    have h2 : (∑' s : ℕ, if c ≤ μ s then (1 : ENNReal) else 0) = (Kc μ c : ENNReal) := by
      rw [tsum_eq_sum (s := hfin.toFinset)]
      · rw [Finset.sum_congr rfl (g := fun _ => (1 : ENNReal))]
        · simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          unfold Kc
          rw [Set.ncard_eq_toFinset_card _ hfin]
        · intro s hs
          rw [Set.Finite.mem_toFinset] at hs
          rw [if_pos (show c ≤ μ s from hs)]
      · intro s hs
        rw [Set.Finite.mem_toFinset] at hs
        rw [if_neg (show ¬ c ≤ μ s from hs)]
    rw [h1, h2]
  · subst hc
    have h1 : ∀ j, (if (0 : ℝ) ≤ msort μ (j + 1) then (1 : ENNReal) else 0) = 1 :=
      fun j => if_pos (msort_nonneg _)
    have h2 : ∀ s, (if (0 : ℝ) ≤ μ s then (1 : ENNReal) else 0) = 1 := fun s => if_pos (hμ0 s)
    simp only [h1, h2]

lemma not_all_le_msort (hμs : Summable μ) (hμ0 : ∀ s, 0 ≤ μ s) {c : ℝ} (hc : 0 < c) :
    ∃ j, 1 ≤ j ∧ msort μ j < c := by
  refine ⟨Kc μ c + 1, by omega, ?_⟩
  by_contra h
  push_neg at h
  have := (msort_iff hμ0 hμs (by omega) hc).1 h
  omega

end ostat

end

end SDOSMain



namespace SDOSMain
open SampleDrivenOS.Structure

noncomputable section

section base
variable {p : ℝ} {q : ℝ → ℕ → ℝ}

lemma Ainf_one (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) : Ainf p q 1 = 0 := by
  rw [Ainf_eq hp0 hp1 hq ⟨⟨hp1.le, le_rfl⟩, mem_Ioi.2 one_pos⟩]; simp

lemma one_mem_Dom (hp1 : p < 1) : (1 : ℝ) ∈ Dom p := ⟨⟨hp1.le, le_rfl⟩, mem_Ioi.2 one_pos⟩

lemma mu_le_one (hq : IsFeasible p q) (hp1 : p < 1) (s : ℕ) : mu p q s ≤ 1 :=
  le_trans (mu_le_tsum (mu_nonneg hq hp1) (mu_summable hq hp1) s) (mu_sum_le hq hp1)

/-- In the case `p = 0`, the function `A` blows up near `0`. -/
lemma blowup (hp1 : (0 : ℝ) < 1) (hq : IsFeasible 0 q) :
    ∃ b ∈ Dom 0, 2 ≤ Ainf 0 q b := by
  have hp0 : (0 : ℝ) ≤ 0 := le_rfl
  have hμ0 := mu_nonneg hq hp1
  have hμs := mu_summable hq hp1
  have hμ1 := mu_sum_le hq hp1
  have hAp := Ainf_props hp0 hp1 hq
  -- Step 1: `A` is not identically zero.
  have hpos : ∃ σ1 ∈ Dom 0, 0 < Ainf 0 q σ1 := by
    by_contra hcon
    push_neg at hcon
    have hz : ∀ σ ∈ Dom (0 : ℝ), Ainf 0 q σ = 0 := fun σ hσ => le_antisymm (hcon σ hσ) (hAp.2.1 σ hσ)
    set c0 := 1 - phi (mu 0 q) 0 with hc0
    have hG : ∀ σ ∈ Dom (0 : ℝ), Gs 0 q σ = c0 * (1 / σ) := by
      intro σ hσ
      unfold Gs integrand; rw [hz σ hσ]; ring
    have hhalf : (1 / 2 : ℝ) ∈ Dom 0 := ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩
    have hA := Ainf_eq hp0 hp1 hq hhalf
    rw [hz _ hhalf] at hA
    have : ∫ σ in (1 / 2 : ℝ)..1, Gs 0 q σ = ∫ σ in (1 / 2 : ℝ)..1, c0 * (1 / σ) := by
      apply intervalIntegral.integral_congr
      intro σ hσ
      rw [uIcc_of_le (by norm_num)] at hσ
      exact hG σ (Dom_sub hhalf hσ)
    rw [this, intervalIntegral.integral_const_mul, integral_one_div_of_pos (by norm_num) one_pos]
      at hA
    have hlog : 0 < Real.log (1 / (1 / 2 : ℝ)) := Real.log_pos (by norm_num)
    have hc0z : c0 = 0 := by
      rcases mul_eq_zero.1 hA.symm with h | h
      · exact h
      · linarith
    -- then every component vanishes
    have hmu : ∀ s, mu 0 q s = 0 := by
      intro s
      apply le_antisymm _ (hμ0 s)
      unfold mu
      rw [intervalIntegral.integral_of_le zero_le_one]
      apply setIntegral_nonpos_ae measurableSet_Ioc
      refine Filter.Eventually.of_forall (fun σ hσ => ?_)
      have hσD : σ ∈ Dom (0 : ℝ) := ⟨⟨hσ.1.le, hσ.2⟩, hσ.1⟩
      have := q_le_Gs hp0 hp1 hq hσD (ℓ := s + 1) (by omega)
      rw [hG σ hσD, hc0z, zero_mul] at this
      exact this
    have hphi0 : phi (mu 0 q) 0 = 0 := by
      unfold phi; simp [hmu]
    rw [hphi0] at hc0
    linarith
  obtain ⟨σ1, hσ1, hA1⟩ := hpos
  set ρ := phi (mu 0 q) (Ainf 0 q σ1) with hρ
  have hρ1 : ρ < 1 := phi_lt_one hμ0 hμs hμ1 hA1
  have hρ0 : 0 ≤ ρ := phi_nonneg _
  have hGlow : ∀ σ ∈ Dom (0 : ℝ), σ ≤ σ1 → (1 - ρ) * (1 / σ) ≤ Gs 0 q σ := by
    intro σ hσ hσσ
    have h1 : Ainf 0 q σ1 ≤ Ainf 0 q σ := hAp.1 hσ hσ1 hσσ
    have h2 := phi_antitone hμ0 hμs h1
    unfold Gs integrand
    rw [mul_one_div]
    apply div_le_div_of_nonneg_right _ hσ.2.le
    linarith
  set a := 2 / (1 - ρ) with ha
  have ha0 : 0 < a := by apply div_pos (by norm_num); linarith
  set δ := σ1 * Real.exp (-a) with hδ
  have hδ0 : 0 < δ := mul_pos hσ1.2 (Real.exp_pos _)
  have hδ1 : δ < σ1 := by
    have : Real.exp (-a) < 1 := by
      have := Real.exp_lt_exp.2 (show -a < 0 by linarith); rwa [Real.exp_zero] at this
    have hσpos : 0 < σ1 := hσ1.2
    nlinarith
  have hδD : δ ∈ Dom (0 : ℝ) := ⟨⟨hδ0.le, le_trans hδ1.le hσ1.1.2⟩, hδ0⟩
  refine ⟨δ, hδD, ?_⟩
  rw [Ainf_eq hp0 hp1 hq hδD]
  have hint1 : IntervalIntegrable (Gs 0 q) volume δ σ1 :=
    hII hδ1.le ((Gs_integrableOn hp0 hp1 hq hδD).mono_set (Icc_subset_Icc_right hσ1.1.2))
  have hint2 : IntervalIntegrable (Gs 0 q) volume σ1 1 :=
    hII hσ1.1.2 (Gs_integrableOn hp0 hp1 hq hσ1)
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have hpos2 : 0 ≤ ∫ σ in σ1..1, Gs 0 q σ := by
    apply intervalIntegral.integral_nonneg hσ1.1.2
    intro σ hσ; exact Gs_nonneg hp1 hq (lt_of_lt_of_le hσ1.2 hσ.1)
  have hlow : ∫ σ in δ..σ1, (1 - ρ) * (1 / σ) ≤ ∫ σ in δ..σ1, Gs 0 q σ := by
    refine intervalIntegral.integral_mono_on hδ1.le ?_ hint1 ?_
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.div continuousOn_const continuousOn_id
      intro σ hσ
      rw [uIcc_of_le hδ1.le] at hσ
      exact (lt_of_lt_of_le hδ0 hσ.1).ne'
    · intro σ hσ
      exact hGlow σ (Dom_sub hδD ⟨hσ.1, le_trans hσ.2 hσ1.1.2⟩) hσ.2
  rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos hδ0 hσ1.2] at hlow
  have hlogv : Real.log (σ1 / δ) = a := by
    rw [hδ, div_mul_eq_div_div, div_self hσ1.2.ne', one_div, ← Real.exp_neg, neg_neg,
      Real.log_exp]
  rw [hlogv] at hlow
  have : (1 - ρ) * a = 2 := by
    have hne : 1 - ρ ≠ 0 := by linarith
    rw [ha]; field_simp
  linarith

lemma exists_base (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) :
    ∃ b, b ∈ Dom p ∧ (∀ s, mu p q s ≤ Ainf p q b) ∧ (∀ x ∈ Dom p, x < b → 1 < Ainf p q x) := by
  rcases hp0.lt_or_eq with hp | hp
  · refine ⟨p, ⟨⟨le_rfl, hp1.le⟩, hp⟩, fun s => mu_le_Ainf_p hp hp1 hq s, ?_⟩
    intro x hx hxp
    exact absurd hx.1.1 (not_le.2 hxp)
  · subst hp
    obtain ⟨b, hb, hb2⟩ := blowup hp1 hq
    refine ⟨b, hb, fun s => ?_, ?_⟩
    · have := mu_le_one hq hp1 s; linarith
    · intro x hx hxb
      have := (Ainf_props hp0 hp1 hq).1 hx hb hxb.le
      linarith

end base

open Classical in
/-- The base point: `A > 1` to its left and `A ≥ μ_s` at it. -/
def bpt (p : ℝ) (q : ℝ → ℕ → ℝ) : ℝ :=
  if h : ∃ b, b ∈ Dom p ∧ (∀ s, mu p q s ≤ Ainf p q b) ∧ (∀ x ∈ Dom p, x < b → 1 < Ainf p q x)
  then h.choose else 1

def thr (p : ℝ) (q : ℝ → ℕ → ℝ) (c : ℝ) : ℝ :=
  sInf {x | x ∈ Icc (bpt p q) 1 ∧ Ainf p q x ≤ c}

def tstar (p : ℝ) (q : ℝ → ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then p else thr p q (msort (mu p q) j)

def qstar (p : ℝ) (q : ℝ → ℕ → ℝ) (σ : ℝ) (ℓ : ℕ) : ℝ :=
  if tstar p q ℓ ≤ σ then Gs p q σ else 0

section thr
variable {p : ℝ} {q : ℝ → ℕ → ℝ}

lemma bpt_spec (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) :
    bpt p q ∈ Dom p ∧ (∀ s, mu p q s ≤ Ainf p q (bpt p q)) ∧
      (∀ x ∈ Dom p, x < bpt p q → 1 < Ainf p q x) := by
  have h := exists_base hp0 hp1 hq
  unfold bpt
  rw [dif_pos h]
  exact h.choose_spec

lemma thr_spec (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {c : ℝ} (hc : 0 ≤ c) :
    thr p q c ∈ Icc (bpt p q) 1 ∧ Ainf p q (thr p q c) ≤ c := by
  have hb := (bpt_spec hp0 hp1 hq).1
  set S := {x | x ∈ Icc (bpt p q) 1 ∧ Ainf p q x ≤ c} with hS
  have hne : S.Nonempty := ⟨1, ⟨hb.1.2, le_rfl⟩, by rw [Ainf_one hp0 hp1 hq]; exact hc⟩
  have hcl : IsClosed S := by
    have := (Ainf_continuousOn hp0 hp1 hq hb).preimage_isClosed_of_isClosed isClosed_Icc
      (isClosed_Iic (a := c))
    exact this
  have hmem : sInf S ∈ S := hcl.csInf_mem hne ⟨bpt p q, fun x hx => hx.1.1⟩
  exact hmem

lemma thr_iff (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {c : ℝ} (hc : 0 ≤ c)
    (hc1 : c ≤ 1) {σ : ℝ} (hσ : σ ∈ Dom p) : thr p q c ≤ σ ↔ Ainf p q σ ≤ c := by
  have hb := bpt_spec hp0 hp1 hq
  have ht := thr_spec hp0 hp1 hq hc
  have htD : thr p q c ∈ Dom p := Dom_sub hb.1 ht.1
  constructor
  · intro h
    exact le_trans ((Ainf_props hp0 hp1 hq).1 htD hσ h) ht.2
  · intro h
    by_cases hσb : bpt p q ≤ σ
    · apply csInf_le ⟨bpt p q, fun x hx => hx.1.1⟩
      exact ⟨⟨hσb, hσ.1.2⟩, h⟩
    · push_neg at hσb
      have := hb.2.2 σ hσ hσb
      linarith

lemma thr_val (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {c : ℝ} (hc : 0 ≤ c)
    (hcb : c ≤ Ainf p q (bpt p q)) : Ainf p q (thr p q c) = c := by
  have hb := bpt_spec hp0 hp1 hq
  have ht := thr_spec hp0 hp1 hq hc
  apply le_antisymm ht.2
  by_contra hlt
  push_neg at hlt
  rcases ht.1.1.lt_or_eq with hgt | heq
  · -- continuity at `thr c` from the left gives a point in the set below `thr c`
    have hcont := (Ainf_continuousOn hp0 hp1 hq hb.1) (thr p q c) ht.1
    have hev : ∀ᶠ y in 𝓝[Icc (bpt p q) 1] (thr p q c), Ainf p q y < c :=
      hcont.eventually_lt_const hlt
    obtain ⟨u, hu, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hev
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hu
    set x := max (bpt p q) (thr p q c - ε / 2) with hx
    have hxlt : x < thr p q c := max_lt hgt (by linarith)
    have hxb : x ∈ Metric.ball (thr p q c) ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · have := le_max_right (bpt p q) (thr p q c - ε / 2); linarith
      · linarith
    have hxI : x ∈ Icc (bpt p q) 1 := ⟨le_max_left _ _, le_trans hxlt.le ht.1.2⟩
    have hAx : Ainf p q x < c := hsub ⟨hball hxb, hxI⟩
    have : thr p q c ≤ x := csInf_le ⟨bpt p q, fun y hy => hy.1.1⟩ ⟨hxI, hAx.le⟩
    linarith
  · rw [← heq] at hlt
    linarith

lemma msort_mu_props (hp1 : p < 1) (hq : IsFeasible p q) {j : ℕ} (hj : 1 ≤ j) :
    0 ≤ msort (mu p q) j ∧ msort (mu p q) j ≤ 1 :=
  ⟨msort_nonneg j, le_trans (msort_le_sum (mu_nonneg hq hp1) (mu_summable hq hp1) hj)
    (mu_sum_le hq hp1)⟩

lemma msort_one_le_base (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) :
    msort (mu p q) 1 ≤ Ainf p q (bpt p q) := by
  have hb := bpt_spec hp0 hp1 hq
  rcases (msort_nonneg (μ := mu p q) 1).lt_or_eq with h | h
  · obtain ⟨s, hs⟩ := msort_one_attained (mu_nonneg hq hp1) (mu_summable hq hp1) h
    exact le_trans hs (hb.2.1 s)
  · rw [← h]; exact (Ainf_props hp0 hp1 hq).2.1 _ hb.1

lemma tstar_zero : tstar p q 0 = p := by simp [tstar]

lemma tstar_pos_eq {j : ℕ} (hj : 1 ≤ j) : tstar p q j = thr p q (msort (mu p q) j) := by
  unfold tstar; rw [if_neg (by omega)]

lemma tstar_ge_b (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {j : ℕ} (hj : 1 ≤ j) :
    bpt p q ≤ tstar p q j ∧ tstar p q j ≤ 1 := by
  rw [tstar_pos_eq hj]
  exact (thr_spec hp0 hp1 hq (msort_mu_props hp1 hq hj).1).1

lemma tstar_dom (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {j : ℕ} (hj : 1 ≤ j) :
    tstar p q j ∈ Dom p := by
  have hb := (bpt_spec hp0 hp1 hq).1
  have := tstar_ge_b hp0 hp1 hq hj
  exact Dom_sub hb ⟨this.1, this.2⟩

lemma tstar_mem (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) (j : ℕ) :
    tstar p q j ∈ Icc p 1 := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; rw [tstar_zero]; exact ⟨le_rfl, hp1.le⟩
  · exact (tstar_dom hp0 hp1 hq h).1

lemma tstar_iff (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {j : ℕ} (hj : 1 ≤ j)
    {σ : ℝ} (hσ : σ ∈ Dom p) : tstar p q j ≤ σ ↔ Ainf p q σ ≤ msort (mu p q) j := by
  rw [tstar_pos_eq hj]
  exact thr_iff hp0 hp1 hq (msort_mu_props hp1 hq hj).1 (msort_mu_props hp1 hq hj).2 hσ

lemma tstar_mono (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) : Monotone (tstar p q) := by
  apply monotone_nat_of_le_succ
  intro j
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    rw [tstar_zero]
    exact (tstar_mem hp0 hp1 hq 1).1
  · -- compare the two thresholds through the characterization
    have hD := tstar_dom hp0 hp1 hq (j := j + 1) (by omega)
    have h1 := (tstar_iff hp0 hp1 hq (j := j + 1) (by omega) hD).1 le_rfl
    have h2 : msort (mu p q) (j + 1) ≤ msort (mu p q) j :=
      msort_anti (mu_nonneg hq hp1) (mu_summable hq hp1) h (by omega)
    exact (tstar_iff hp0 hp1 hq h hD).2 (le_trans h1 h2)

lemma tstar_one_val (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) :
    Ainf p q (tstar p q 1) = msort (mu p q) 1 := by
  rw [tstar_pos_eq le_rfl]
  exact thr_val hp0 hp1 hq (msort_nonneg 1) (msort_one_le_base hp0 hp1 hq)

end thr

end

end SDOSMain



namespace SDOSMain
open SampleDrivenOS.Structure

noncomputable section

section qs
variable {p : ℝ} {q : ℝ → ℕ → ℝ}

lemma Gs_aemeasurable (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {S : Set ℝ}
    (hS : MeasurableSet S) (hSD : S ⊆ Dom p) : AEMeasurable (Gs p q) (volume.restrict S) := by
  have hBm : AEMeasurable (Ainf p q) (volume.restrict S) :=
    aemeasurable_restrict_of_antitoneOn hS ((Ainf_props hp0 hp1 hq).1.mono hSD)
  unfold Gs integrand
  exact (aemeasurable_const.sub ((phi_continuous (mu_nonneg hq hp1)
    (mu_summable hq hp1)).measurable.comp_aemeasurable hBm)).div aemeasurable_id

lemma Ioc_sub_Dom (hp0 : 0 ≤ p) {τ : ℝ} (hτ : τ ≤ 1) : Ioc p τ ⊆ Dom p :=
  fun σ hσ => ⟨⟨hσ.1.le, le_trans hσ.2 hτ⟩, lt_of_le_of_lt hp0 hσ.1⟩

lemma thr_mu_props (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) (s : ℕ) :
    thr p q (mu p q s) ∈ Dom p ∧ p ≤ thr p q (mu p q s) ∧
      Ainf p q (thr p q (mu p q s)) = mu p q s := by
  have hb := bpt_spec hp0 hp1 hq
  have ht := thr_spec hp0 hp1 hq (mu_nonneg hq hp1 s)
  exact ⟨Dom_sub hb.1 ht.1, le_trans hb.1.1.1 ht.1.1,
    thr_val hp0 hp1 hq (mu_nonneg hq hp1 s) (hb.2.1 s)⟩

/-- Mass of one "unsorted" component up to `τ`. -/
lemma piece_mass (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {τ : ℝ} (hτ : τ ∈ Dom p)
    (s : ℕ) :
    ∫⁻ σ in Ioc p τ, (Ici (thr p q (mu p q s))).indicator
        (fun σ => ENNReal.ofReal (Gs p q σ)) σ =
      ENNReal.ofReal (max (mu p q s - max (Ainf p q τ) 0) 0) := by
  rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  obtain ⟨huD, hpu, hAu⟩ := thr_mu_props hp0 hp1 hq s
  set u := thr p q (mu p q s) with hu
  have hAτ0 : 0 ≤ Ainf p q τ := (Ainf_props hp0 hp1 hq).2.1 τ hτ
  have hiff := thr_iff hp0 hp1 hq (mu_nonneg hq hp1 s) (mu_le_one hq hp1 s) hτ
  by_cases huτ : u ≤ τ
  · have hset : (Ici u ∩ Ioc p τ : Set ℝ) =ᵐ[(volume : Measure ℝ)] (Icc u τ : Set ℝ) := by
      rcases hpu.lt_or_eq with h | h
      · have : Ici u ∩ Ioc p τ = Icc u τ := by
          ext x; simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
          constructor
          · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
          · rintro ⟨h1, h3⟩; exact ⟨h1, lt_of_lt_of_le h h1, h3⟩
        rw [this]
        exact Filter.EventuallyEq.rfl
      · have : Ici u ∩ Ioc p τ = Ioc u τ := by
          ext x; simp only [mem_inter_iff, mem_Ici, mem_Ioc]
          rw [← h]
          constructor
          · rintro ⟨_, h2, h3⟩; exact ⟨h2, h3⟩
          · rintro ⟨h2, h3⟩; exact ⟨h2.le, h2, h3⟩
        rw [this]; exact Ioc_ae_eq_Icc
    rw [setLIntegral_congr hset]
    have hint : IntegrableOn (Gs p q) (Icc u τ) :=
      (Gs_integrableOn hp0 hp1 hq huD).mono_set (Icc_subset_Icc_right hτ.1.2)
    rw [← ofReal_integral_eq_lintegral_ofReal hint]
    · congr 1
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huτ]
      have hA1 := Ainf_eq hp0 hp1 hq huD
      have hA2 := Ainf_eq hp0 hp1 hq hτ
      have e := intervalIntegral.integral_add_adjacent_intervals (hII huτ hint)
        (hII hτ.1.2 (Gs_integrableOn hp0 hp1 hq hτ))
      have hle : Ainf p q τ ≤ mu p q s := hiff.1 huτ
      rw [max_eq_left hAτ0, max_eq_left (by linarith)]
      linarith
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall (fun σ hσ =>
        Gs_nonneg hp1 hq (lt_of_lt_of_le huD.2 hσ.1))
  · have : Ici u ∩ Ioc p τ = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_empty_iff_false, iff_false]
      rintro ⟨h1, _, h3⟩; exact huτ (le_trans h1 h3)
    rw [this]
    simp only [Measure.restrict_empty, lintegral_zero_measure]
    have : mu p q s < Ainf p q τ := by
      by_contra h; push_neg at h; exact huτ (hiff.2 h)
    rw [max_eq_left hAτ0, max_eq_right (by linarith), ENNReal.ofReal_zero]

/-- The cumulative mass of the improved solution is `φ(A(τ))`. -/
lemma cumMass_qstar (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {τ : ℝ}
    (hτ : τ ∈ Dom p) :
    cumMass p (qstar p q) τ = ENNReal.ofReal (phi (mu p q) (Ainf p q τ)) := by
  have hμ0 := mu_nonneg hq hp1
  have hμs := mu_summable hq hp1
  unfold cumMass
  rw [setLIntegral_congr (Ioc_ae_eq_Icc (a := p) (b := τ)).symm]
  rw [setLIntegral_congr_fun measurableSet_Ioc
    (g := fun σ => ∑' s : ℕ, (Ici (thr p q (mu p q s))).indicator
      (fun σ => ENNReal.ofReal (Gs p q σ)) σ)]
  · rw [lintegral_tsum]
    · simp_rw [piece_mass hp0 hp1 hq hτ]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun s => phi_term_nonneg s _)
        (phi_summable hμ0 hμs _)]
      rfl
    · intro s
      exact ((Gs_aemeasurable hp0 hp1 hq measurableSet_Ioc
        (Ioc_sub_Dom hp0 hτ.1.2)).ennreal_ofReal).indicator measurableSet_Ici
  · intro σ hσ
    have hσD : σ ∈ Dom p := Ioc_sub_Dom hp0 hτ.1.2 hσ
    have hA0 : 0 ≤ Ainf p q σ := (Ainf_props hp0 hp1 hq).2.1 σ hσD
    have h1 : ∀ j : ℕ, ENNReal.ofReal (qstar p q σ (j + 1)) =
        ENNReal.ofReal (Gs p q σ) * (if Ainf p q σ ≤ msort (mu p q) (j + 1) then 1 else 0) := by
      intro j
      have hi := tstar_iff hp0 hp1 hq (j := j + 1) (by omega) hσD
      unfold qstar
      by_cases h : tstar p q (j + 1) ≤ σ
      · rw [if_pos h, if_pos (hi.1 h), mul_one]
      · rw [if_neg h, if_neg (fun h' => h (hi.2 h')), mul_zero, ENNReal.ofReal_zero]
    have h2 : ∀ s : ℕ, (Ici (thr p q (mu p q s))).indicator
        (fun σ => ENNReal.ofReal (Gs p q σ)) σ =
        ENNReal.ofReal (Gs p q σ) * (if Ainf p q σ ≤ mu p q s then 1 else 0) := by
      intro s
      have hi := thr_iff hp0 hp1 hq (hμ0 s) (mu_le_one hq hp1 s) hσD
      by_cases h : thr p q (mu p q s) ≤ σ
      · rw [indicator_of_mem (show σ ∈ Ici _ from h), if_pos (hi.1 h), mul_one]
      · rw [indicator_of_notMem (show σ ∉ Ici _ from h), if_neg (fun h' => h (hi.2 h')),
          mul_zero]
    show ∑' j : ℕ, ENNReal.ofReal (qstar p q σ (j + 1)) = _
    simp_rw [h1, h2, ENNReal.tsum_mul_left]
    rw [count_eq hμ0 hμs hA0]

lemma cumMass_at_p (p : ℝ) (q' : ℝ → ℕ → ℝ) : cumMass p q' p = 0 := by
  unfold cumMass
  rw [Icc_self]
  exact setLIntegral_measure_zero _ _ (measure_singleton p)

lemma qstar_nonneg (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {σ : ℝ} {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) : 0 ≤ qstar p q σ ℓ := by
  unfold qstar
  split_ifs with h
  · exact Gs_nonneg hp1 hq (lt_of_lt_of_le (tstar_dom hp0 hp1 hq hℓ).2 h)
  · exact le_rfl

theorem qstar_feasible (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) :
    IsFeasible p (qstar p q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t _ ℓ hℓ; exact qstar_nonneg hp0 hp1 hq hℓ
  · intro ℓ hℓ
    have htD := tstar_dom hp0 hp1 hq hℓ
    have hpt : p ≤ tstar p q ℓ := htD.1.1
    have heq : (fun t => qstar p q t ℓ) = (Ici (tstar p q ℓ)).indicator (Gs p q) := by
      funext t
      unfold qstar
      by_cases h : tstar p q ℓ ≤ t
      · rw [if_pos h, indicator_of_mem (show t ∈ Ici _ from h)]
      · rw [if_neg h, indicator_of_notMem (show t ∉ Ici _ from h)]
    rw [heq]
    unfold IntegrableOn
    rw [integrable_indicator_iff measurableSet_Ici]
    unfold IntegrableOn
    rw [Measure.restrict_restrict measurableSet_Ici]
    have : Ici (tstar p q ℓ) ∩ Icc p 1 = Icc (tstar p q ℓ) 1 := by
      ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, le_trans hpt h1, h3⟩
    rw [this]
    exact Gs_integrableOn hp0 hp1 hq htD
  · intro t ht ℓ hℓ
    by_cases htD : t ∈ Dom p
    · rw [cumMass_qstar hp0 hp1 hq htD]
      have hφ0 := phi_nonneg (μ := mu p q) (Ainf p q t)
      have hφ1 : phi (mu p q) (Ainf p q t) ≤ 1 :=
        le_trans (phi_le_sum (mu_nonneg hq hp1) (mu_summable hq hp1) _) (mu_sum_le hq hp1)
      unfold qstar
      split_ifs with h
      · rw [Gs_mul t htD.2, ← ENNReal.ofReal_add (by linarith) hφ0]
        simp
      · rw [mul_zero, ENNReal.ofReal_zero, zero_add]
        exact ENNReal.ofReal_le_one.2 hφ1
    · -- `t = 0 = p`
      have ht0 : t = p := by
        by_contra hne
        exact htD ⟨ht, lt_of_le_of_lt hp0 (lt_of_le_of_ne ht.1 (Ne.symm hne))⟩
      subst ht0
      rw [cumMass_at_p]
      have : qstar t q t ℓ = 0 := by
        unfold qstar
        rw [if_neg]
        intro h
        apply htD
        exact Dom_sub (tstar_dom hp0 hp1 hq hℓ) ⟨h, ht.2⟩ |> fun hh => by
          have := (tstar_dom hp0 hp1 hq hℓ).2
          exact ⟨ht, lt_of_lt_of_le this h⟩
      rw [this, mul_zero, ENNReal.ofReal_zero, zero_add]
      exact zero_le_one

theorem qstar_eq56 (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) :
    SolvesEq5Eq6 p (tstar p q) (qstar p q) := by
  intro ℓ hℓ τ hτ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hτD : τ ∈ Dom p := ⟨⟨hτ.1, hτ.2.le⟩, lt_of_lt_of_le (tstar_dom hp0 hp1 hq hℓ).2 h⟩
    rw [cumMass_qstar hp0 hp1 hq hτD]
    have hφ0 := phi_nonneg (μ := mu p q) (Ainf p q τ)
    have hφ1 : phi (mu p q) (Ainf p q τ) ≤ 1 :=
      le_trans (phi_le_sum (mu_nonneg hq hp1) (mu_summable hq hp1) _) (mu_sum_le hq hp1)
    unfold qstar
    rw [if_pos h, Gs_mul τ hτD.2, ← ENNReal.ofReal_add (by linarith) hφ0]
    simp
  · unfold qstar; rw [if_neg (not_le.2 h)]

end qs

end

end SDOSMain



namespace SDOSMain
open SampleDrivenOS.Structure

noncomputable section

lemma nbTerm_continuous (k ℓ : ℕ) : Continuous (nbTerm k ℓ) := by
  unfold nbTerm
  fun_prop

lemma nbTerm_nonneg (k ℓ : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ nbTerm k ℓ t := by
  unfold nbTerm
  apply Finset.sum_nonneg
  intro j _
  have : 0 ≤ 1 - t := by linarith [ht.2]
  have : 0 ≤ t := ht.1
  positivity

/-- Indicator-type function `g · 1[s ≤ t]`. -/
def cut (s : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ := if s ≤ t then g t else 0

lemma cut_eq_indicator (s : ℝ) (g : ℝ → ℝ) : cut s g = (Ici s).indicator g := by
  funext t; unfold cut
  by_cases h : s ≤ t
  · rw [if_pos h, indicator_of_mem (show t ∈ Ici s from h)]
  · rw [if_neg h, indicator_of_notMem (show t ∉ Ici s from h)]

lemma cut_integrableOn {p s : ℝ} {g : ℝ → ℝ} (hps : p ≤ s) (hg : IntegrableOn g (Icc s 1)) :
    IntegrableOn (cut s g) (Icc p 1) := by
  rw [cut_eq_indicator]
  unfold IntegrableOn
  rw [integrable_indicator_iff measurableSet_Ici]
  unfold IntegrableOn
  rw [Measure.restrict_restrict measurableSet_Ici]
  have : Ici s ∩ Icc p 1 = Icc s 1 := by
    ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, le_trans hps h1, h3⟩
  rw [this]; exact hg

/-- Moving the mass of one component to the right end under a ceiling `g` does not decrease
the integral against a non-decreasing weight. -/
lemma comp_le {p s : ℝ} {f g w : ℝ → ℝ} (hp0 : 0 ≤ p) (hps : p ≤ s) (hs1 : s ≤ 1)
    (hwc : Continuous w) (hwmono : MonotoneOn w (Icc 0 1))
    (hf0 : ∀ t ∈ Icc p 1, 0 ≤ f t) (hfint : IntegrableOn f (Icc p 1))
    (hgint : IntegrableOn g (Icc s 1)) (hfg : ∀ t ∈ Icc s 1, f t ≤ g t)
    (hmass : ∫ t in p..1, f t = ∫ t in s..1, g t) :
    ∫ t in p..1, f t * w t ≤ ∫ t in p..1, cut s g t * w t := by
  have hIcc : ∀ t ∈ Icc p 1, t ∈ Icc (0 : ℝ) 1 := fun t ht => ⟨le_trans hp0 ht.1, ht.2⟩
  have hsI : s ∈ Icc p 1 := ⟨hps, hs1⟩
  have hfwint : IntegrableOn (fun t => f t * w t) (Icc p 1) :=
    hfint.mul_continuousOn_of_subset hwc.continuousOn measurableSet_Icc isCompact_Icc subset_rfl
  have hgwint : IntegrableOn (fun t => g t * w t) (Icc s 1) :=
    hgint.mul_continuousOn_of_subset hwc.continuousOn measurableSet_Icc isCompact_Icc subset_rfl
  have hfwI1 : IntervalIntegrable (fun t => f t * w t) volume p s :=
    hII hps (hfwint.mono_set (Icc_subset_Icc_right hs1))
  have hfwI2 : IntervalIntegrable (fun t => f t * w t) volume s 1 :=
    hII hs1 (hfwint.mono_set (Icc_subset_Icc_left hps))
  have hfI1 : IntervalIntegrable f volume p s := hII hps (hfint.mono_set (Icc_subset_Icc_right hs1))
  have hfI2 : IntervalIntegrable f volume s 1 := hII hs1 (hfint.mono_set (Icc_subset_Icc_left hps))
  have hgI : IntervalIntegrable g volume s 1 := hII hs1 hgint
  have hgwI : IntervalIntegrable (fun t => g t * w t) volume s 1 := hII hs1 hgwint
  have hmoved : ∫ t in p..1, cut s g t * w t = ∫ t in s..1, g t * w t := by
    have hm1 : ∫ t in p..s, cut s g t * w t = 0 := by
      have : ∫ t in p..s, cut s g t * w t = ∫ t in p..s, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae'
        · filter_upwards [Measure.ae_ne volume s] with t hts htI
          have : t < s := lt_of_le_of_ne htI.2 hts
          simp [cut, not_le.2 this]
        · exact Filter.Eventually.of_forall (fun x hx =>
            absurd (lt_of_lt_of_le hx.1 (le_trans hx.2 hps)) (lt_irrefl _))
      rw [this]; simp
    have hm2 : ∫ t in s..1, cut s g t * w t = ∫ t in s..1, g t * w t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hs1] at ht
      simp [cut, ht.1]
    have hI1 : IntervalIntegrable (fun t => cut s g t * w t) volume p s := by
      have : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume p s := intervalIntegrable_const
      refine this.congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_uIoc,
        ae_restrict_of_ae (Measure.ae_ne volume s)] with t htI hts
      rw [uIoc_of_le hps] at htI
      have : t < s := lt_of_le_of_ne htI.2 hts
      simp [cut, not_le.2 this]
    have hI2 : IntervalIntegrable (fun t => cut s g t * w t) volume s 1 := by
      refine hgwI.congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t htI
      rw [uIoc_of_le hs1] at htI
      simp [cut, htI.1.le]
    rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2, hm1, hm2, zero_add]
  rw [hmoved, ← intervalIntegral.integral_add_adjacent_intervals hfwI1 hfwI2]
  have hA : ∫ t in p..s, f t * w t ≤ ∫ t in p..s, w s * f t := by
    apply intervalIntegral.integral_mono_on hps hfwI1 (hfI1.const_mul _)
    intro t ht
    have ht1 : t ∈ Icc p 1 := ⟨ht.1, le_trans ht.2 hs1⟩
    have hwts : w t ≤ w s := hwmono (hIcc t ht1) (hIcc s hsI) ht.2
    have hq0 : 0 ≤ f t := hf0 t ht1
    nlinarith
  have hB : ∫ t in s..1, f t * w t ≤ ∫ t in s..1, (g t * w t - w s * (g t - f t)) := by
    apply intervalIntegral.integral_mono_on hs1 hfwI2 (hgwI.sub ((hgI.sub hfI2).const_mul _))
    intro t ht
    have ht1 : t ∈ Icc p 1 := ⟨le_trans hps ht.1, ht.2⟩
    have hwts : w s ≤ w t := hwmono (hIcc s hsI) (hIcc t ht1) ht.1
    have hqG : f t ≤ g t := hfg t ht
    nlinarith
  have hB' : ∫ t in s..1, (g t * w t - w s * (g t - f t)) =
      (∫ t in s..1, g t * w t) - w s * ((∫ t in s..1, g t) - ∫ t in s..1, f t) := by
    rw [intervalIntegral.integral_sub hgwI ((hgI.sub hfI2).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hgI hfI2]
  have hA' : ∫ t in p..s, w s * f t = w s * ∫ t in p..s, f t :=
    intervalIntegral.integral_const_mul _ _
  have hsplit : ∫ t in p..1, f t = (∫ t in p..s, f t) + ∫ t in s..1, f t :=
    (intervalIntegral.integral_add_adjacent_intervals hfI1 hfI2).symm
  rw [hB'] at hB
  rw [hA'] at hA
  rw [hsplit] at hmass
  have : w s * (∫ t in p..s, f t) - w s * ((∫ t in s..1, g t) - ∫ t in s..1, f t) = 0 := by
    rw [← mul_sub]
    have : (∫ t in p..s, f t) - ((∫ t in s..1, g t) - ∫ t in s..1, f t) = 0 := by linarith
    rw [this, mul_zero]
  linarith

/-- Rearrangement: on an antitone weight, a set of `n` indices in `[1,k]` sums to at most the
first `n` weights. -/
lemma sum_subset_le_initial (w : ℕ → ℝ) (hw : ∀ a b, 1 ≤ a → a ≤ b → w b ≤ w a) :
    ∀ (k : ℕ) (S : Finset ℕ), S ⊆ Finset.Icc 1 k →
      ∑ ℓ ∈ S, w ℓ ≤ ∑ ℓ ∈ Finset.Icc 1 S.card, w ℓ := by
  intro k
  induction k with
  | zero =>
    intro S hS
    have : S = ∅ := by
      ext x; simp only [Finset.notMem_empty, iff_false]
      intro hx; have := hS hx; simp at this
    subst this; simp
  | succ k ih =>
    intro S hS
    by_cases hk : k + 1 ∈ S
    · set S' := S.erase (k + 1) with hS'
      have hS'sub : S' ⊆ Finset.Icc 1 k := by
        intro x hx
        rw [Finset.mem_erase] at hx
        have := hS hx.2
        simp only [Finset.mem_Icc] at this ⊢
        omega
      have hcard : S.card = S'.card + 1 := by
        rw [hS', Finset.card_erase_of_mem hk]
        have : 0 < S.card := Finset.card_pos.2 ⟨_, hk⟩
        omega
      have hcardle : S'.card ≤ k := by
        have := Finset.card_le_card hS'sub
        simpa using this
      rw [← Finset.add_sum_erase S w hk, hcard, Finset.sum_Icc_succ_top (by omega)]
      have h1 := ih S' hS'sub
      have h2 : w (k + 1) ≤ w (S'.card + 1) := hw _ _ (by omega) (by omega)
      linarith
    · have hS' : S ⊆ Finset.Icc 1 k := by
        intro x hx
        have := hS hx
        simp only [Finset.mem_Icc] at this ⊢
        refine ⟨this.1, ?_⟩
        rcases Nat.lt_or_eq_of_le this.2 with h | h
        · omega
        · subst h; exact absurd hx hk
      exact ih S hS'

end

end SDOSMain



namespace SDOSMain
open SampleDrivenOS.Structure

noncomputable section

section fk
variable {p : ℝ} {q : ℝ → ℕ → ℝ}

lemma qstar_eq_cut (ℓ : ℕ) : (fun σ => qstar p q σ ℓ) = cut (tstar p q ℓ) (Gs p q) := by
  funext σ; rfl

/-- Pointwise sorting inequality. -/
lemma sort_pointwise (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {k : ℕ} (hk : 1 ≤ k)
    {σ : ℝ} (hσ : σ ∈ Dom p) :
    ∑ ℓ ∈ Finset.Icc 1 k, cut (thr p q (mu p q (ℓ - 1))) (Gs p q) σ * nbTerm k ℓ σ ≤
      ∑ ℓ ∈ Finset.Icc 1 k, qstar p q σ ℓ * nbTerm k ℓ σ := by
  have hμ0 := mu_nonneg hq hp1
  have hμs := mu_summable hq hp1
  set c := Ainf p q σ with hc
  have hc0 : 0 ≤ c := (Ainf_props hp0 hp1 hq).2.1 σ hσ
  have hG0 : 0 ≤ Gs p q σ := Gs_nonneg hp1 hq hσ.2
  have hσI : σ ∈ Icc (0 : ℝ) 1 := ⟨hσ.2.le, hσ.1.2⟩
  set w := fun ℓ => nbTerm k ℓ σ with hw
  have hw0 : ∀ ℓ, 0 ≤ w ℓ := fun ℓ => nbTerm_nonneg k ℓ hσI
  have hwanti : ∀ a b, 1 ≤ a → a ≤ b → w b ≤ w a := fun a b ha hab =>
    lemma_18 k hk σ hσI (mem_Ici.2 ha) (mem_Ici.2 (le_trans ha hab)) hab
  -- rewrite both sides as `G σ` times a sum over a filter
  have hL : ∀ ℓ ∈ Finset.Icc 1 k, cut (thr p q (mu p q (ℓ - 1))) (Gs p q) σ * nbTerm k ℓ σ =
      Gs p q σ * (if c ≤ mu p q (ℓ - 1) then w ℓ else 0) := by
    intro ℓ _
    have hi := thr_iff hp0 hp1 hq (hμ0 (ℓ - 1)) (mu_le_one hq hp1 (ℓ - 1)) hσ
    unfold cut
    by_cases h : thr p q (mu p q (ℓ - 1)) ≤ σ
    · rw [if_pos h, if_pos (hi.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (hi.2 h'))]; ring
  have hR : ∀ ℓ ∈ Finset.Icc 1 k, qstar p q σ ℓ * nbTerm k ℓ σ =
      Gs p q σ * (if c ≤ msort (mu p q) ℓ then w ℓ else 0) := by
    intro ℓ hℓ
    rw [Finset.mem_Icc] at hℓ
    have hi := tstar_iff hp0 hp1 hq hℓ.1 hσ
    unfold qstar
    by_cases h : tstar p q ℓ ≤ σ
    · rw [if_pos h, if_pos (hi.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (hi.2 h'))]; ring
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, ← Finset.mul_sum, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hG0
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  set S := (Finset.Icc 1 k).filter (fun ℓ => c ≤ mu p q (ℓ - 1)) with hS
  set R := (Finset.Icc 1 k).filter (fun ℓ => c ≤ msort (mu p q) ℓ) with hRdef
  have hSsub : S ⊆ Finset.Icc 1 k := Finset.filter_subset _ _
  rcases hc0.lt_or_eq with hcpos | hczero
  · -- `c > 0`
    have hfin := Kset_finite hμs hcpos
    have hcardK : S.card ≤ Kc (mu p q) c := by
      have himg : S.image (fun ℓ => ℓ - 1) ⊆ hfin.toFinset := by
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨ℓ, hℓ, rfl⟩ := hx
        rw [Set.Finite.mem_toFinset]
        exact (Finset.mem_filter.1 hℓ).2
      have hinj : Set.InjOn (fun ℓ => ℓ - 1) S := by
        intro a ha b hb hab
        have ha1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 ha).1).1
        have hb1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 hb).1).1
        simp only at hab; omega
      have := Finset.card_le_card himg
      rw [Finset.card_image_of_injOn hinj] at this
      unfold Kc
      rw [Set.ncard_eq_toFinset_card _ hfin]
      exact this
    have hcardk : S.card ≤ k := by
      have := Finset.card_le_card hSsub; simpa using this
    have h1 := sum_subset_le_initial w hwanti k S hSsub
    have h2 : Finset.Icc 1 S.card ⊆ R := by
      intro ℓ hℓ
      rw [Finset.mem_Icc] at hℓ
      rw [hRdef, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hℓ.1, le_trans hℓ.2 hcardk⟩, ?_⟩
      rw [msort_iff hμ0 hμs hℓ.1 hcpos]
      omega
    have h3 : ∑ ℓ ∈ Finset.Icc 1 S.card, w ℓ ≤ ∑ ℓ ∈ R, w ℓ :=
      Finset.sum_le_sum_of_subset_of_nonneg h2 (fun ℓ _ _ => hw0 ℓ)
    linarith
  · -- `c = 0`: every order statistic qualifies
    have hRall : R = Finset.Icc 1 k := by
      rw [hRdef]; apply Finset.filter_true_of_mem
      intro ℓ _; rw [← hczero]; exact msort_nonneg ℓ
    rw [hRall]
    exact Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun ℓ _ _ => hw0 ℓ)

theorem Fk_le (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {k : ℕ} (hk : 1 ≤ k) :
    Fk p q k ≤ Fk p (qstar p q) k := by
  unfold Fk
  have hμ0 := mu_nonneg hq hp1
  -- Step 1: per-component comparison with the unsorted moved solution
  have step1 : ∀ ℓ ∈ Finset.Icc 1 k, ∫ t in p..1, q t ℓ * nbTerm k ℓ t ≤
      ∫ t in p..1, cut (thr p q (mu p q (ℓ - 1))) (Gs p q) t * nbTerm k ℓ t := by
    intro ℓ hℓ
    rw [Finset.mem_Icc] at hℓ
    obtain ⟨s, rfl⟩ : ∃ s, ℓ = s + 1 := ⟨ℓ - 1, by omega⟩
    have hs1 : s + 1 - 1 = s := by omega
    rw [hs1]
    obtain ⟨huD, hpu, hAu⟩ := thr_mu_props hp0 hp1 hq s
    apply comp_le hp0 hpu huD.1.2 (nbTerm_continuous k (s + 1))
      (lemma_17 k (s + 1) hk hℓ.1 hℓ.2)
    · intro t ht; exact hq.1 t ht _ hℓ.1
    · exact hq.2.1 _ hℓ.1
    · exact Gs_integrableOn hp0 hp1 hq huD
    · intro t ht
      exact q_le_Gs hp0 hp1 hq (Dom_sub huD ht) hℓ.1
    · rw [← Ainf_eq hp0 hp1 hq huD, hAu]; rfl
  refine le_trans (Finset.sum_le_sum step1) ?_
  -- Step 2: sorting, pointwise under the integral
  have hint1 : ∀ ℓ ∈ Finset.Icc 1 k, IntervalIntegrable
      (fun t => cut (thr p q (mu p q (ℓ - 1))) (Gs p q) t * nbTerm k ℓ t) volume p 1 := by
    intro ℓ _
    obtain ⟨huD, hpu, _⟩ := thr_mu_props hp0 hp1 hq (ℓ - 1)
    apply hII hp1.le
    exact (cut_integrableOn hpu (Gs_integrableOn hp0 hp1 hq huD)).mul_continuousOn_of_subset
      (nbTerm_continuous k ℓ).continuousOn measurableSet_Icc isCompact_Icc subset_rfl
  have hint2 : ∀ ℓ ∈ Finset.Icc 1 k, IntervalIntegrable
      (fun t => qstar p q t ℓ * nbTerm k ℓ t) volume p 1 := by
    intro ℓ hℓ
    rw [Finset.mem_Icc] at hℓ
    have htD := tstar_dom hp0 hp1 hq hℓ.1
    apply hII hp1.le
    have : IntegrableOn (fun t => qstar p q t ℓ) (Icc p 1) :=
      (qstar_feasible hp0 hp1 hq).2.1 ℓ hℓ.1
    exact this.mul_continuousOn_of_subset
      (nbTerm_continuous k ℓ).continuousOn measurableSet_Icc isCompact_Icc subset_rfl
  rw [← intervalIntegral.integral_finsetSum hint1, ← intervalIntegral.integral_finsetSum hint2]
  refine intervalIntegral.integral_mono_on hp1.le ?_ ?_ ?_
  · have := IntervalIntegrable.sum (Finset.Icc 1 k) hint1
    rw [Finset.sum_fn] at this; exact this
  · have := IntervalIntegrable.sum (Finset.Icc 1 k) hint2
    rw [Finset.sum_fn] at this; exact this
  intro σ hσ
  by_cases hσD : σ ∈ Dom p
  · exact sort_pointwise hp0 hp1 hq hk hσD
  · -- `σ = 0 = p`: both sides vanish
    have hσ0 : σ ≤ 0 := by
      by_contra h; push_neg at h; exact hσD ⟨hσ, h⟩
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    rw [Finset.mem_Icc] at hℓ
    obtain ⟨huD, _, _⟩ := thr_mu_props hp0 hp1 hq (ℓ - 1)
    have htD := tstar_dom hp0 hp1 hq hℓ.1
    have e1 : cut (thr p q (mu p q (ℓ - 1))) (Gs p q) σ = 0 := by
      unfold cut; rw [if_neg]; intro h; have := huD.2; simp only [mem_Ioi] at this; linarith
    have e2 : qstar p q σ ℓ = 0 := by
      unfold qstar; rw [if_neg]; intro h; have := htD.2; simp only [mem_Ioi] at this; linarith
    rw [e1, e2]

end fk

end

end SDOSMain



namespace SDOSMain
open SampleDrivenOS.Structure

noncomputable section

section tf
variable {p : ℝ} {q : ℝ → ℕ → ℝ}

lemma interval_K (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {i : ℕ} (hi : 1 ≤ i)
    {σ : ℝ} (hσ : σ ∈ Dom p) (h1 : tstar p q i ≤ σ) (h2 : σ < tstar p q (i + 1)) :
    0 < Ainf p q σ ∧ Kc (mu p q) (Ainf p q σ) = i := by
  have hμ0 := mu_nonneg hq hp1
  have hμs := mu_summable hq hp1
  have a1 := (tstar_iff hp0 hp1 hq hi hσ).1 h1
  have a2 : ¬ Ainf p q σ ≤ msort (mu p q) (i + 1) :=
    fun h => absurd ((tstar_iff hp0 hp1 hq (j := i + 1) (by omega) hσ).2 h) (not_le.2 h2)
  push_neg at a2
  have hpos : 0 < Ainf p q σ := lt_of_le_of_lt (msort_nonneg _) a2
  refine ⟨hpos, ?_⟩
  have b1 := (msort_iff hμ0 hμs hi hpos).1 a1
  have b2 : ¬ i + 1 ≤ Kc (mu p q) (Ainf p q σ) :=
    fun h => absurd ((msort_iff hμ0 hμs (by omega) hpos).2 h) (not_le.2 a2)
  omega

lemma phi_finite (hp1 : p < 1) (hq : IsFeasible p q) {c : ℝ} (hc : 0 < c) (F : Finset ℕ)
    (hF : (F : Set ℕ) = Kset (mu p q) c) :
    phi (mu p q) c = (∑ s ∈ F, mu p q s) - F.card * c := by
  unfold phi
  rw [max_eq_left hc.le]
  rw [tsum_eq_sum (s := F)]
  · have : ∀ s ∈ F, max (mu p q s - c) 0 = mu p q s - c := by
      intro s hs
      have : s ∈ (F : Set ℕ) := hs
      rw [hF] at this
      exact max_eq_left (by simp only [Kset, mem_setOf_eq] at this; linarith)
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib]
    simp
  · intro s hs
    have : s ∉ (F : Set ℕ) := hs
    rw [hF] at this
    simp only [Kset, mem_setOf_eq, not_le] at this
    exact max_eq_right (by linarith)

lemma Kset_const (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {i : ℕ} (hi : 1 ≤ i)
    {σ σ' : ℝ} (hσ : σ ∈ Dom p) (hσ' : σ' ∈ Dom p) (h1 : tstar p q i ≤ σ)
    (h2 : σ' < tstar p q (i + 1)) (hle : σ ≤ σ') :
    Kset (mu p q) (Ainf p q σ) = Kset (mu p q) (Ainf p q σ') := by
  have hμs := mu_summable hq hp1
  have k1 := interval_K hp0 hp1 hq hi hσ h1 (lt_of_le_of_lt hle h2)
  have k2 := interval_K hp0 hp1 hq hi hσ' (le_trans h1 hle) h2
  have hA : Ainf p q σ' ≤ Ainf p q σ := (Ainf_props hp0 hp1 hq).1 hσ hσ' hle
  have hsub : Kset (mu p q) (Ainf p q σ) ⊆ Kset (mu p q) (Ainf p q σ') := by
    intro s hs; simp only [Kset, mem_setOf_eq] at hs ⊢; linarith
  apply Set.eq_of_subset_of_ncard_le hsub _ (Kset_finite hμs k2.1)
  have e1 := k1.2; have e2 := k2.2
  unfold Kc at e1 e2
  omega

lemma hasDerivAt_Ainf (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {a : ℝ} (ha : a ∈ Dom p)
    {σ : ℝ} (hσ : σ ∈ Ioo a 1) : HasDerivAt (Ainf p q) (-Gs p q σ) σ := by
  have hσD : σ ∈ Dom p := Dom_sub ha ⟨hσ.1.le, hσ.2.le⟩
  have hcont : ContinuousOn (Gs p q) (Ioo a 1) :=
    (Gs_continuousOn hp0 hp1 hq ha).mono Ioo_subset_Icc_self
  have hFTC := intervalIntegral.integral_hasDerivAt_left
    (hII hσD.1.2 (Gs_integrableOn hp0 hp1 hq hσD))
    (hcont.stronglyMeasurableAtFilter isOpen_Ioo σ hσ)
    (hcont.continuousAt (Ioo_mem_nhds hσ.1 hσ.2))
  apply hFTC.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hσ.1 hσ.2] with u hu
  exact Ainf_eq hp0 hp1 hq (Dom_sub ha ⟨hu.1.le, hu.2.le⟩)

/-- Constant of the interval: `c_i = Σ_{s ∈ S_i} μ_s`. -/
lemma interval_phi (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {i : ℕ} (hi : 1 ≤ i)
    (hlt : tstar p q i < tstar p q (i + 1)) :
    ∃ C : ℝ, ∀ σ ∈ Ico (tstar p q i) (tstar p q (i + 1)),
      phi (mu p q) (Ainf p q σ) = C - i * Ainf p q σ := by
  have hμs := mu_summable hq hp1
  have htD := tstar_dom hp0 hp1 hq hi
  have k0 := interval_K hp0 hp1 hq hi htD le_rfl hlt
  set F := (Kset_finite hμs k0.1).toFinset with hF
  refine ⟨∑ s ∈ F, mu p q s, fun σ hσ => ?_⟩
  have hσD : σ ∈ Dom p := Dom_sub htD ⟨hσ.1, le_trans hσ.2.le (tstar_mem hp0 hp1 hq _).2⟩
  have kσ := interval_K hp0 hp1 hq hi hσD hσ.1 hσ.2
  have hK := Kset_const hp0 hp1 hq hi htD hσD le_rfl hσ.2 hσ.1
  have hFσ : (F : Set ℕ) = Kset (mu p q) (Ainf p q σ) := by
    rw [hF, Set.Finite.coe_toFinset, hK]
  rw [phi_finite hp1 hq kσ.1 F hFσ]
  have hcard : F.card = i := by
    have := k0.2
    unfold Kc at this
    rw [Set.ncard_eq_toFinset_card _ (Kset_finite hμs k0.1)] at this
    exact this
  rw [hcard]

lemma ODE_const (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {i : ℕ} (hi : 1 ≤ i)
    (hlt : tstar p q i < tstar p q (i + 1)) :
    (∀ σ ∈ Ico (tstar p q i) (tstar p q (i + 1)),
      σ ^ (i + 1) * Gs p q σ = tstar p q i ^ (i + 1) * Gs p q (tstar p q i)) ∧
    tstar p q (i + 1) ^ (i + 1) * Gs p q (tstar p q (i + 1)) =
      tstar p q i ^ (i + 1) * Gs p q (tstar p q i) := by
  have hμ0 := mu_nonneg hq hp1
  have hμs := mu_summable hq hp1
  set a := tstar p q i with ha
  set b := tstar p q (i + 1) with hb
  have haD : a ∈ Dom p := tstar_dom hp0 hp1 hq hi
  have hb1 : b ≤ 1 := (tstar_mem hp0 hp1 hq (i + 1)).2
  have hbD : b ∈ Dom p := tstar_dom hp0 hp1 hq (by omega)
  obtain ⟨C, hC⟩ := interval_phi hp0 hp1 hq hi hlt
  set h : ℝ → ℝ := fun σ => σ ^ i * (1 - C + i * Ainf p q σ) with hh
  have hAc : ContinuousOn (Ainf p q) (Icc a b) :=
    (Ainf_continuousOn hp0 hp1 hq haD).mono (Icc_subset_Icc_right hb1)
  have hhc : ContinuousOn h (Icc a b) := by
    apply ContinuousOn.mul (continuousOn_pow i)
    exact continuousOn_const.add (continuousOn_const.mul hAc)
  -- `σ G(σ) = 1 - C + i A(σ)` on `[a, b)`
  have hkey : ∀ σ ∈ Ico a b, σ * Gs p q σ = 1 - C + i * Ainf p q σ := by
    intro σ hσ
    have hσD : σ ∈ Dom p := Dom_sub haD ⟨hσ.1, le_trans hσ.2.le hb1⟩
    rw [Gs_mul σ hσD.2, hC σ hσ]; ring
  have hconst : ∀ x ∈ Icc a b, h x = h a := by
    intro x hx
    rcases hx.1.lt_or_eq with hax | hax
    · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope h
        (fun y => i * y ^ (i - 1) * (1 - C + i * Ainf p q y) + y ^ i * (i * (-Gs p q y)))
        hax (hhc.mono (Icc_subset_Icc_right hx.2)) (by
          intro y hy
          have hyA : y ∈ Ioo a 1 := ⟨hy.1, lt_of_lt_of_le hy.2 (le_trans hx.2 hb1)⟩
          have hd := hasDerivAt_Ainf hp0 hp1 hq haD hyA
          have := (hasDerivAt_pow i y).mul ((hd.const_mul (i : ℝ)).const_add (1 - C))
          exact this)
      have hξI : ξ ∈ Ico a b := ⟨hξ.1.le, lt_of_lt_of_le hξ.2 hx.2⟩
      have hξ0 : 0 < ξ := lt_trans haD.2 hξ.1
      have hzero : (i : ℝ) * ξ ^ (i - 1) * (1 - C + i * Ainf p q ξ) +
          ξ ^ i * (i * (-Gs p q ξ)) = 0 := by
        rw [← hkey ξ hξI]
        obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        push_cast
        ring
      rw [hzero] at hslope
      have hne : x - a ≠ 0 := by linarith
      field_simp at hslope
      linarith
    · rw [hax]
  have hval : ∀ σ ∈ Ico a b, σ ^ (i + 1) * Gs p q σ = h σ := by
    intro σ hσ
    simp only [hh]
    rw [← hkey σ hσ]; ring
  refine ⟨fun σ hσ => ?_, ?_⟩
  · rw [hval σ hσ, hval a ⟨le_rfl, hlt⟩, hconst σ ⟨hσ.1, hσ.2.le⟩]
  · -- endpoint: extend `φ(A σ) = C - i A σ` to `σ = b` by continuity
    have hFc : ContinuousOn (fun σ => phi (mu p q) (Ainf p q σ) - (C - i * Ainf p q σ))
        (Icc a b) := by
      apply ContinuousOn.sub ((phi_continuous hμ0 hμs).comp_continuousOn hAc)
      exact continuousOn_const.sub (continuousOn_const.mul hAc)
    have hmem : b ∈ closure (Ico a b) := by
      rw [closure_Ico hlt.ne]; exact ⟨hlt.le, le_rfl⟩
    have hcw := ((hFc b ⟨hlt.le, le_rfl⟩).mono Ico_subset_Icc_self).mem_closure_image hmem
    have himg : (fun σ => phi (mu p q) (Ainf p q σ) - (C - i * Ainf p q σ)) '' Ico a b ⊆
        {0} := by
      rintro _ ⟨σ, hσ, rfl⟩
      simp only [mem_singleton_iff]
      rw [hC σ hσ]; ring
    have hb0 := closure_mono himg hcw
    rw [closure_singleton, mem_singleton_iff] at hb0
    have hbkey : b * Gs p q b = 1 - C + i * Ainf p q b := by
      rw [Gs_mul b hbD.2]; linarith
    have : b ^ (i + 1) * Gs p q b = h b := by
      simp only [hh]; rw [← hbkey]; ring
    rw [this, hconst b ⟨hlt.le, le_rfl⟩, ← hval a ⟨le_rfl, hlt⟩]

def Dval (p : ℝ) (q : ℝ → ℕ → ℝ) (i : ℕ) : ℝ := tstar p q i ^ (i + 1) * Gs p q (tstar p q i)

lemma Dval_succ (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {i : ℕ} (hi : 1 ≤ i) :
    Dval p q (i + 1) = tstar p q (i + 1) * Dval p q i := by
  unfold Dval
  have hmono := tstar_mono hp0 hp1 hq (Nat.le_succ i)
  rcases hmono.lt_or_eq with hlt | heq
  · rw [← (ODE_const hp0 hp1 hq hi hlt).2]; ring
  · rw [← heq]; ring

lemma phi_msort_one (hp1 : p < 1) (hq : IsFeasible p q) : phi (mu p q) (msort (mu p q) 1) = 0 := by
  have hμ0 := mu_nonneg hq hp1
  have hμs := mu_summable hq hp1
  unfold phi
  rw [max_eq_left (msort_nonneg 1)]
  have : ∀ s, max (mu p q s - msort (mu p q) 1) 0 = 0 := by
    intro s
    have := mu_le_msort_one hμ0 hμs s
    exact max_eq_right (by linarith)
  simp [this]

lemma Dval_one (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) : Dval p q 1 = tstar p q 1 := by
  unfold Dval
  have hD := tstar_dom hp0 hp1 hq (le_refl 1)
  have h1 : tstar p q 1 ^ (1 + 1) * Gs p q (tstar p q 1) =
      tstar p q 1 * (tstar p q 1 * Gs p q (tstar p q 1)) := by ring
  rw [h1, Gs_mul _ hD.2, tstar_one_val hp0 hp1 hq, phi_msort_one hp1 hq]; ring

lemma Dval_eq (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {i : ℕ} (hi : 1 ≤ i) :
    Dval p q i = thresholdProd (tstar p q) i := by
  induction i, hi using Nat.le_induction with
  | base =>
    rw [Dval_one hp0 hp1 hq]; unfold thresholdProd; simp
  | succ n hn ih =>
    rw [Dval_succ hp0 hp1 hq hn, ih]
    unfold thresholdProd
    rw [Finset.prod_Icc_succ_top (by omega)]
    ring

lemma Gs_on_interval (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {i : ℕ} (hi : 1 ≤ i)
    {σ : ℝ} (h1 : tstar p q i ≤ σ) (h2 : σ < tstar p q (i + 1)) :
    Gs p q σ = thresholdProd (tstar p q) i / σ ^ (i + 1) := by
  have hlt : tstar p q i < tstar p q (i + 1) := lt_of_le_of_lt h1 h2
  have hσ0 : 0 < σ := lt_of_lt_of_le (tstar_dom hp0 hp1 hq hi).2 h1
  have := (ODE_const hp0 hp1 hq hi hlt).1 σ ⟨h1, h2⟩
  rw [← Dval_eq hp0 hp1 hq hi]
  unfold Dval
  rw [← this]
  field_simp

lemma Gs_tail_zero (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) {τ : ℝ}
    (hτ : τ ∈ Ico p 1) (hall : ∀ i, tstar p q i ≤ τ) : Gs p q τ = 0 := by
  have hμ0 := mu_nonneg hq hp1
  have hμs := mu_summable hq hp1
  have hτD : τ ∈ Dom p := ⟨⟨hτ.1, hτ.2.le⟩, lt_of_lt_of_le (tstar_dom hp0 hp1 hq le_rfl).2 (hall 1)⟩
  have hAp := Ainf_props hp0 hp1 hq
  have hA0 : Ainf p q τ = 0 := by
    rcases (hAp.2.1 τ hτD).lt_or_eq with hpos | hz
    · obtain ⟨j, hj, hlt⟩ := not_all_le_msort hμs hμ0 hpos
      have := (tstar_iff hp0 hp1 hq hj hτD).1 (hall j)
      linarith
    · exact hz.symm
  have hzero : ∀ σ ∈ Icc τ 1, Ainf p q σ = 0 := by
    intro σ hσ
    have := hAp.1 hτD (Dom_sub hτD hσ) hσ.1
    have := hAp.2.1 σ (Dom_sub hτD hσ)
    linarith
  set c0 := 1 - phi (mu p q) 0 with hc0
  have hG : ∀ σ ∈ Icc τ 1, Gs p q σ = c0 * (1 / σ) := by
    intro σ hσ
    unfold Gs integrand; rw [hzero σ hσ]; ring
  have hA := Ainf_eq hp0 hp1 hq hτD
  rw [hA0] at hA
  have : ∫ σ in τ..1, Gs p q σ = ∫ σ in τ..1, c0 * (1 / σ) := by
    apply intervalIntegral.integral_congr
    intro σ hσ
    rw [uIcc_of_le hτ.2.le] at hσ
    exact hG σ hσ
  rw [this, intervalIntegral.integral_const_mul, integral_one_div_of_pos hτD.2 one_pos] at hA
  have hlog : 0 < Real.log (1 / τ) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hτD.2]; linarith [hτ.2]
  have hc : c0 = 0 := by
    rcases mul_eq_zero.1 hA.symm with h | h
    · exact h
    · linarith
  rw [hG τ ⟨le_rfl, hτ.2.le⟩, hc, zero_mul]

theorem qstar_threshold (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : IsFeasible p q) :
    IsThresholdForm p (tstar p q) (qstar p q) := by
  intro τ hτ ℓ hℓ
  refine ⟨fun i h1 h2 => ⟨fun hli => ?_, fun hil => ?_⟩, fun hno => ?_⟩
  · have hi : 1 ≤ i := le_trans hℓ hli
    have hle : tstar p q ℓ ≤ τ := le_trans (tstar_mono hp0 hp1 hq hli) h1
    unfold qstar
    rw [if_pos hle]
    exact Gs_on_interval hp0 hp1 hq hi h1 h2
  · have : τ < tstar p q ℓ := lt_of_lt_of_le h2 (tstar_mono hp0 hp1 hq hil)
    unfold qstar
    rw [if_neg (not_le.2 this)]
  · have hall : ∀ i, tstar p q i ≤ τ := by
      intro i
      induction i with
      | zero => rw [tstar_zero]; exact hτ.1
      | succ n ih =>
        by_contra h
        exact hno n ⟨ih, not_le.1 h⟩
    unfold qstar
    rw [if_pos (hall ℓ)]
    exact Gs_tail_zero hp0 hp1 hq hτ hall

end tf

end

end SDOSMain

open SampleDrivenOS.Structure in
theorem solution (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (q : ℝ → ℕ → ℝ) (hq : IsFeasible p q) :
    ∃ qstar : ℝ → ℕ → ℝ, ∃ t : ℕ → ℝ,
      IsFeasible p qstar ∧
      (∀ k : ℕ, 1 ≤ k → Fk p q k ≤ Fk p qstar k) ∧
      Monotone t ∧ t 0 = p ∧ (∀ i : ℕ, t i ∈ Set.Icc p 1) ∧
      SolvesEq5Eq6 p t qstar ∧
      IsThresholdForm p t qstar :=
  ⟨SDOSMain.qstar p q, SDOSMain.tstar p q,
    SDOSMain.qstar_feasible hp0 hp1 hq,
    fun _ hk => SDOSMain.Fk_le hp0 hp1 hq hk,
    SDOSMain.tstar_mono hp0 hp1 hq,
    SDOSMain.tstar_zero,
    SDOSMain.tstar_mem hp0 hp1 hq,
    SDOSMain.qstar_eq56 hp0 hp1 hq,
    SDOSMain.qstar_threshold hp0 hp1 hq⟩
