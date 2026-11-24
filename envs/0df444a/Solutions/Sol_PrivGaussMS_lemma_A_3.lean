-- Prove2me | solution 1 for PrivGaussMS.lemma_A_3
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T16:28:08.165015+00:00
-- url     : https://prove2.me/submissions/7f51b78e-80ca-4027-bfc3-7f72f97b8ae6

import Mathlib
import Definitions.Def_PrivGaussMS_Basics
import Definitions.Def_FoundationsRL_DECLower_tvDist

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem solution {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] {n : ℕ}
    (ε : ℝ) (hε : 0 ≤ ε) :
    (∀ (ν : Measure Ω) (p q : Ω → ℝ≥0∞) (G : Set Ω) (δ : ℝ), 0 ≤ δ → Measurable p →
        Measurable q → MeasurableSet G → IsProbabilityMeasure (ν.withDensity p) →
        IsProbabilityMeasure (ν.withDensity q) → (ν.withDensity p).real Gᶜ ≤ δ →
        (∀ᵐ z ∂ν, z ∈ G → p z ≤ ENNReal.ofReal (Real.exp ε) * q z) →
        ∀ E : Set Ω, MeasurableSet E →
          (ν.withDensity p).real E ≤ Real.exp ε * (ν.withDensity q).real E + δ) ∧
    (∀ (M Mt : (Fin n → X) → Measure Y) (δ τ : ℝ), 0 ≤ δ → PrivGaussMS.IsDPM M ε δ →
        (∀ x, IsProbabilityMeasure (Mt x)) →
        (∀ x, FoundationsRL.DECLower.tvDist (M x) (Mt x) ≤ τ) →
        PrivGaussMS.IsDPM Mt ε (δ + (1 + Real.exp ε) * τ)) ∧
    (∀ (M C : (Fin n → X) → Measure Y) (w δ₀ : ℝ), 0 ≤ w → w ≤ 1 → 0 ≤ δ₀ →
        PrivGaussMS.IsDPM M ε δ₀ →
        (∀ x, IsProbabilityMeasure (C x)) →
        PrivGaussMS.IsDPM (fun x => ENNReal.ofReal w • M x + ENNReal.ofReal (1 - w) • C x) ε
          (w * δ₀ + 1 - w)) := by
  have hexp : 0 ≤ Real.exp ε := (Real.exp_pos ε).le
  refine ⟨?_, ?_, ?_⟩
  · intro ν p q G δ hδ hp hq hG hP hQ hGc hpq E hE
    have h1 : ν.withDensity p (E ∩ G) ≤ ENNReal.ofReal (Real.exp ε) * ν.withDensity q E := by
      calc ν.withDensity p (E ∩ G) = ∫⁻ z in E ∩ G, p z ∂ν := withDensity_apply _ (hE.inter hG)
        _ ≤ ∫⁻ z in E ∩ G, ENNReal.ofReal (Real.exp ε) * q z ∂ν :=
            setLIntegral_mono_ae' (hE.inter hG) (hpq.mono fun z hz hzs => hz hzs.2)
        _ = ENNReal.ofReal (Real.exp ε) * ∫⁻ z in E ∩ G, q z ∂ν := lintegral_const_mul _ hq
        _ = ENNReal.ofReal (Real.exp ε) * ν.withDensity q (E ∩ G) := by
            rw [withDensity_apply _ (hE.inter hG)]
        _ ≤ ENNReal.ofReal (Real.exp ε) * ν.withDensity q E := by
            gcongr; exact Set.inter_subset_left
    have h2 : ν.withDensity p Gᶜ ≤ ENNReal.ofReal δ := by
      rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hδ]; exact hGc
    have h3 : ν.withDensity p E ≤
        ENNReal.ofReal (Real.exp ε) * ν.withDensity q E + ENNReal.ofReal δ := by
      calc ν.withDensity p E = ν.withDensity p (E ∩ G) + ν.withDensity p (E \ G) :=
            (measure_inter_add_sdiff E hG).symm
        _ ≤ _ := add_le_add h1 (le_trans (measure_mono fun z hz => hz.2) h2)
    have hne : ENNReal.ofReal (Real.exp ε) * ν.withDensity q E + ENNReal.ofReal δ ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _),
        ENNReal.ofReal_ne_top⟩
    have h4 := ENNReal.toReal_mono hne h3
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      ENNReal.ofReal_ne_top, ENNReal.toReal_mul, ENNReal.toReal_ofReal hexp,
      ENNReal.toReal_ofReal hδ] at h4
    simpa only [measureReal_def] using h4
  · intro M Mt δ τ hδ hM hMt hTV
    obtain ⟨hMp, hdp⟩ := hM
    refine ⟨hMt, ?_⟩
    intro S S' hS O hO
    have hdp' : (M S).real O ≤ Real.exp ε * (M S').real O + δ := hdp S S' hS O hO
    show (Mt S).real O ≤ Real.exp ε * (Mt S').real O + (δ + (1 + Real.exp ε) * τ)
    have tv : ∀ x, |(M x).real O - (Mt x).real O| ≤ τ := fun x => by
      haveI := hMp x
      haveI := hMt x
      refine le_trans ?_ (hTV x)
      unfold FoundationsRL.DECLower.tvDist
      have hb : BddAbove (Set.range fun s : {s : Set Y // MeasurableSet s} =>
          |((M x) s.1).toReal - ((Mt x) s.1).toReal|) := by
        refine ⟨1, ?_⟩
        rintro _ ⟨s, rfl⟩
        have a1 : ((M x) s.1).toReal ≤ 1 := measureReal_le_one
        have a2 : ((Mt x) s.1).toReal ≤ 1 := measureReal_le_one
        have a3 : 0 ≤ ((M x) s.1).toReal := ENNReal.toReal_nonneg
        have a4 : 0 ≤ ((Mt x) s.1).toReal := ENNReal.toReal_nonneg
        show |((M x) s.1).toReal - ((Mt x) s.1).toReal| ≤ 1
        rw [abs_le]; constructor <;> linarith
      exact le_ciSup hb ⟨O, hO⟩
    have t1 := abs_le.1 (tv S)
    have t2 := abs_le.1 (tv S')
    have t3 : Real.exp ε * (M S').real O ≤ Real.exp ε * ((Mt S').real O + τ) :=
      mul_le_mul_of_nonneg_left (by linarith [t2.1]) hexp
    nlinarith [t1.1, t1.2]
  · intro M C w δ₀ hw0 hw1 hδ₀ hM hC
    obtain ⟨hMp, hdp⟩ := hM
    have key : ∀ x (O : Set Y),
        (ENNReal.ofReal w • M x + ENNReal.ofReal (1 - w) • C x).real O =
          w * (M x).real O + (1 - w) * (C x).real O := by
      intro x O
      haveI := hMp x
      haveI := hC x
      simp only [measureReal_def, Measure.coe_add, Measure.coe_smul, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)), ENNReal.toReal_mul,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal hw0, ENNReal.toReal_ofReal (by linarith)]
    have hprob : ∀ x, IsProbabilityMeasure
        (ENNReal.ofReal w • M x + ENNReal.ofReal (1 - w) • C x) := by
      intro x
      haveI := hMp x
      haveI := hC x
      constructor
      simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        measure_univ, mul_one]
      rw [← ENNReal.ofReal_add hw0 (by linarith)]
      simp
    refine ⟨hprob, ?_⟩
    intro S S' hS O hO
    show (ENNReal.ofReal w • M S + ENNReal.ofReal (1 - w) • C S).real O ≤
      Real.exp ε * (ENNReal.ofReal w • M S' + ENNReal.ofReal (1 - w) • C S').real O +
        (w * δ₀ + 1 - w)
    rw [key, key]
    have hdp' : (M S).real O ≤ Real.exp ε * (M S').real O + δ₀ := hdp S S' hS O hO
    haveI := hC S
    haveI := hC S'
    have c1 : (C S).real O ≤ 1 := measureReal_le_one
    have c2 : 0 ≤ (C S').real O := measureReal_nonneg
    have e1 : w * (M S).real O ≤ w * (Real.exp ε * (M S').real O + δ₀) :=
      mul_le_mul_of_nonneg_left hdp' hw0
    have e2 : (1 - w) * (C S).real O ≤ (1 - w) * 1 :=
      mul_le_mul_of_nonneg_left c1 (by linarith)
    have e3 : 0 ≤ Real.exp ε * ((1 - w) * (C S').real O) :=
      mul_nonneg hexp (mul_nonneg (by linarith) c2)
    nlinarith
