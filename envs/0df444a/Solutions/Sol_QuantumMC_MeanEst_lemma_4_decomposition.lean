-- Prove2me | solution 1 for QuantumMC.MeanEst.lemma_4_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T18:28:05.113583+00:00
-- url     : https://prove2.me/submissions/2022583c-cab2-41df-9648-a3171b0f4f6b

import Mathlib
import Definitions.Def_QuantumMC_MeanEst_Setting

open MeasureTheory ProbabilityTheory Filter
set_option linter.unusedVariables false

open QuantumMC.MeanEst

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P)
    (hpos : ∀ ω, 0 ≤ X ω) (k : ℕ) :
    (∫ ω, X ω ∂P) = (∫ ω, truncIco 0 1 X ω ∂P) +
      (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * (∫ ω, band X ℓ ω ∂P)) +
      (∫ ω, truncGe ((2 : ℝ) ^ k) X ω ∂P) := by
  have haesmI : ∀ c d : ℝ, AEStronglyMeasurable (truncIco c d X) P := by
    intro c d
    have hXa : AEMeasurable X P := hX.aestronglyMeasurable.aemeasurable
    refine (show AEMeasurable (truncIco c d X) P from
      ⟨truncIco c d (hXa.mk X), ?_, ?_⟩).aestronglyMeasurable
    · unfold truncIco
      exact Measurable.ite
        ((measurableSet_le measurable_const hXa.measurable_mk).inter
          (measurableSet_lt hXa.measurable_mk measurable_const))
        hXa.measurable_mk measurable_const
    · filter_upwards [hXa.ae_eq_mk] with ω hω
      simp only [truncIco, hω]
  have haesmG : ∀ y : ℝ, AEStronglyMeasurable (truncGe y X) P := by
    intro y
    have hXa : AEMeasurable X P := hX.aestronglyMeasurable.aemeasurable
    refine (show AEMeasurable (truncGe y X) P from
      ⟨truncGe y (hXa.mk X), ?_, ?_⟩).aestronglyMeasurable
    · unfold truncGe
      exact Measurable.ite (measurableSet_le measurable_const hXa.measurable_mk)
        hXa.measurable_mk measurable_const
    · filter_upwards [hXa.ae_eq_mk] with ω hω
      simp only [truncGe, hω]
  have hTrI : ∀ c d ω, 0 ≤ truncIco c d X ω ∧ truncIco c d X ω ≤ X ω := by
    intro c d ω
    by_cases h : c ≤ X ω ∧ X ω < d
    · simp only [truncIco, if_pos h]; exact ⟨hpos ω, le_refl _⟩
    · simp only [truncIco, if_neg h]; exact ⟨le_refl 0, hpos ω⟩
  have hTrG : ∀ y ω, 0 ≤ truncGe y X ω ∧ truncGe y X ω ≤ X ω := by
    intro y ω
    by_cases h : y ≤ X ω
    · simp only [truncGe, if_pos h]; exact ⟨hpos ω, le_refl _⟩
    · simp only [truncGe, if_neg h]; exact ⟨le_refl 0, hpos ω⟩
  have hband : ∀ ℓ ω, (2 : ℝ) ^ ℓ * band X ℓ ω =
      truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X ω := by
    intro ℓ ω
    rw [band, ← mul_div_assoc, mul_div_cancel_left₀ _ (pow_ne_zero ℓ (by norm_num))]
  have hgeom : ∀ v : ℝ, 0 ≤ v → ∀ ω,
      truncGe v X ω = truncIco v (2 * v) X ω + truncGe (2 * v) X ω := by
    intro v hv ω
    by_cases h1 : v ≤ X ω
    · by_cases h2 : X ω < 2 * v
      · rw [truncGe, if_pos h1, truncIco, if_pos ⟨h1, h2⟩,
          truncGe, if_neg (not_le.mpr h2)]
        ring
      · rw [truncGe, if_pos h1, truncIco, if_neg (fun hc => h2 hc.2),
          truncGe, if_pos (not_lt.mp h2)]
        ring
    · have h2v : ¬ 2 * v ≤ X ω := fun h => h1 (le_trans (by linarith) h)
      rw [truncGe, if_neg h1, truncIco, if_neg (fun hc => h1 hc.1),
        truncGe, if_neg h2v]
      ring
  have hbase : ∀ ω, 0 ≤ X ω → X ω = truncIco 0 1 X ω + truncGe 1 X ω := by
    intro ω hx
    rcases lt_or_ge (X ω) 1 with h | h
    · rw [truncIco, if_pos ⟨hx, h⟩, truncGe, if_neg (not_le.mpr h)]
      ring
    · rw [truncIco, if_neg (fun hc : (0 : ℝ) ≤ X ω ∧ X ω < 1 => not_lt.mpr h hc.2),
        truncGe, if_pos h]
      ring
  have hmain : ∀ k, ∀ ω, 0 ≤ X ω →
      X ω = truncIco 0 1 X ω +
        (∑ ℓ ∈ Finset.Icc 1 k, truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X ω) +
        truncGe ((2 : ℝ) ^ k) X ω := by
    intro k
    induction k with
    | zero =>
      intro ω hx
      simpa using hbase ω hx
    | succ n ih =>
      intro ω hx
      have hstep := hgeom ((2 : ℝ) ^ n) (by positivity) ω
      have hpow : (2 : ℝ) * (2 : ℝ) ^ n = (2 : ℝ) ^ (n + 1) := by
        rw [pow_succ]; ring
      rw [ih ω hx, hstep, hpow]
      rw [Finset.sum_Icc_succ_top (f := fun ℓ => truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X ω)
        (show 1 ≤ n + 1 by omega)]
      simp only [Nat.add_sub_cancel]
      ring
  have hsum_eq : ∀ ω, (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * band X ℓ ω)
      = ∑ ℓ ∈ Finset.Icc 1 k, truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X ω :=
    fun ω => Finset.sum_congr rfl (fun ℓ _ => hband ℓ ω)
  have hpt : ∀ ω, 0 ≤ X ω → X ω = truncIco 0 1 X ω +
      (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * band X ℓ ω) +
      truncGe ((2 : ℝ) ^ k) X ω := by
    intro ω hx
    rw [hmain k ω hx, hsum_eq ω]
  have hT0int : Integrable (fun ω => truncIco 0 1 X ω) P :=
    Integrable.mono' hX (haesmI 0 1) (Eventually.of_forall (fun ω => by
      rw [Real.norm_of_nonneg (hTrI 0 1 ω).1]
      exact (hTrI 0 1 ω).2))
  have hTkint : Integrable (fun ω => truncGe ((2 : ℝ) ^ k) X ω) P :=
    Integrable.mono' hX (haesmG _) (Eventually.of_forall (fun ω => by
      rw [Real.norm_of_nonneg (hTrG _ ω).1]
      exact (hTrG _ ω).2))
  have hFint : ∀ ℓ, Integrable (fun ω => (2 : ℝ) ^ ℓ * band X ℓ ω) P := by
    intro ℓ
    have hcong : (fun ω => truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X ω)
        =ᵐ[P] (fun ω => (2 : ℝ) ^ ℓ * band X ℓ ω) :=
      Eventually.of_forall (fun ω => (hband ℓ ω).symm)
    have haesm : AEStronglyMeasurable (fun ω => (2 : ℝ) ^ ℓ * band X ℓ ω) P :=
      (haesmI _ _).congr hcong
    refine Integrable.mono' hX haesm (Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_of_nonneg (by rw [hband ℓ ω]; exact (hTrI _ _ ω).1),
      hband ℓ ω]
    exact (hTrI _ _ ω).2
  have hGint : Integrable (fun ω => ∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * band X ℓ ω) P :=
    integrable_finsetSum _ (fun ℓ _ => hFint ℓ)
  have hae : X =ᵐ[P] (fun ω => truncIco 0 1 X ω +
      (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * band X ℓ ω) +
      truncGe ((2 : ℝ) ^ k) X ω) :=
    Eventually.of_forall (fun ω => hpt ω (hpos ω))
  calc ∫ ω, X ω ∂P
      = ∫ ω, (truncIco 0 1 X ω + (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * band X ℓ ω) +
            truncGe ((2 : ℝ) ^ k) X ω) ∂P := integral_congr_ae hae
    _ = (∫ ω, truncIco 0 1 X ω + (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * band X ℓ ω) ∂P)
          + ∫ ω, truncGe ((2 : ℝ) ^ k) X ω ∂P :=
        integral_add (hT0int.add hGint) hTkint
    _ = ((∫ ω, truncIco 0 1 X ω ∂P)
          + ∫ ω, (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * band X ℓ ω) ∂P)
          + ∫ ω, truncGe ((2 : ℝ) ^ k) X ω ∂P := by
        rw [integral_add hT0int hGint]
    _ = ((∫ ω, truncIco 0 1 X ω ∂P)
          + (∑ ℓ ∈ Finset.Icc 1 k, ∫ ω, (2 : ℝ) ^ ℓ * band X ℓ ω ∂P))
          + ∫ ω, truncGe ((2 : ℝ) ^ k) X ω ∂P := by
        rw [integral_finsetSum (Finset.Icc 1 k) (fun ℓ _ => hFint ℓ)]
    _ = ((∫ ω, truncIco 0 1 X ω ∂P)
          + (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * (∫ ω, band X ℓ ω ∂P)))
          + ∫ ω, truncGe ((2 : ℝ) ^ k) X ω ∂P := by
        rw [show (∑ ℓ ∈ Finset.Icc 1 k, ∫ ω, (2 : ℝ) ^ ℓ * band X ℓ ω ∂P)
            = ∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * (∫ ω, band X ℓ ω ∂P) from
            Finset.sum_congr rfl (fun ℓ _ => integral_const_mul _ _)]
