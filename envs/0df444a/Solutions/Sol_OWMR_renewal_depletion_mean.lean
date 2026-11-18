-- Prove2me | solution 1 for OWMR.renewal_depletion_mean
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T02:43:06.13501+00:00
-- url     : https://prove2.me/submissions/bfbc412e-5c36-44f4-8132-0e605656f489

import Theorems.Thm_OWMR_renewal_interval_bound
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Lemma 2, mean-depletion bound `𝔼 X_w ≤ w/2`, in the form `∫_{[0,w)} y U(dy) ≤ (w/2) M(w)`, from
the interval bound `U[x, w) ≤ M(w - x)` of the same lemma. By Tonelli's theorem,
`∫_{[0,w)} y U(dy) = ∫_0^w U[x,w) dx ≤ ∫_0^w M(w - x) dx = ∫_{[0,w)} (w - y) U(dy)`, and the two
outer integrals add up to `w M(w)`.
-/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

/-- Tonelli's theorem for a measurable set of pairs, with `U` restricted to `A` in the first
coordinate and Lebesgue measure restricted to `B` in the second. -/
private lemma swap_count (U : Measure ℝ) [SFinite U] (A B : Set ℝ) {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S) :
    ∫⁻ y in A, ((volume : Measure ℝ).restrict B) (Prod.mk y ⁻¹' S) ∂U
      = ∫⁻ t in B, (U.restrict A) ((fun y => (y, t)) ⁻¹' S) := by
  rw [← Measure.prod_apply hS, Measure.prod_apply_symm hS]

theorem solution (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) (hw : 0 ≤ w) :
    ∫⁻ x in Set.Ico 0 w, ENNReal.ofReal x ∂(renewalMeasure ρ)
      ≤ ENNReal.ofReal (w / 2) * renewalMeasure ρ (Set.Ico 0 w) := by
  have : SFinite (renewalMeasure ρ) := by unfold renewalMeasure; infer_instance
  have hS1 : MeasurableSet {q : ℝ × ℝ | q.2 ≤ q.1} :=
    measurableSet_le measurable_snd measurable_fst
  have hS2 : MeasurableSet {q : ℝ × ℝ | q.1 < w - q.2} :=
    measurableSet_lt measurable_fst (measurable_const.sub measurable_snd)
  -- `∫_{[0,w)} y U(dy) = ∫_0^w U[t, w) dt`
  have hI : ∫⁻ y in Set.Ico 0 w, ENNReal.ofReal y ∂(renewalMeasure ρ)
      = ∫⁻ t in Set.Ico 0 w, renewalMeasure ρ (Set.Ico t w) := by
    calc ∫⁻ y in Set.Ico 0 w, ENNReal.ofReal y ∂(renewalMeasure ρ)
        = ∫⁻ y in Set.Ico 0 w, ((volume : Measure ℝ).restrict (Set.Ico 0 w))
            (Prod.mk y ⁻¹' {q : ℝ × ℝ | q.2 ≤ q.1}) ∂(renewalMeasure ρ) := by
          refine setLIntegral_congr_fun measurableSet_Ico fun y hy => ?_
          have e : Prod.mk y ⁻¹' {q : ℝ × ℝ | q.2 ≤ q.1} = Set.Iic y := by ext t; simp
          have e2 : Set.Iic y ∩ Set.Ico 0 w = Set.Icc 0 y := by
            ext t
            simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ico, Set.mem_Icc]
            constructor
            · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
            · rintro ⟨h1, h2⟩; exact ⟨h2, h1, lt_of_le_of_lt h2 hy.2⟩
          rw [e, Measure.restrict_apply measurableSet_Iic, e2, Real.volume_Icc, sub_zero]
      _ = ∫⁻ t in Set.Ico 0 w, ((renewalMeasure ρ).restrict (Set.Ico 0 w))
            ((fun y => (y, t)) ⁻¹' {q : ℝ × ℝ | q.2 ≤ q.1}) := swap_count _ _ _ hS1
      _ = ∫⁻ t in Set.Ico 0 w, renewalMeasure ρ (Set.Ico t w) := by
          refine setLIntegral_congr_fun measurableSet_Ico fun t ht => ?_
          have e : (fun y => (y, t)) ⁻¹' {q : ℝ × ℝ | q.2 ≤ q.1} = Set.Ici t := by ext y; simp
          have e2 : Set.Ici t ∩ Set.Ico 0 w = Set.Ico t w := by
            ext y
            simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ico]
            constructor
            · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
            · rintro ⟨h1, h2⟩; exact ⟨h1, ht.1.trans h1, h2⟩
          rw [e, Measure.restrict_apply measurableSet_Ici, e2]
  -- `∫_{[0,w)} (w - y) U(dy) = ∫_0^w M(w - t) dt`
  have hK : ∫⁻ y in Set.Ico 0 w, ENNReal.ofReal (w - y) ∂(renewalMeasure ρ)
      = ∫⁻ t in Set.Ico 0 w, renewalMeasure ρ (Set.Ico 0 (w - t)) := by
    calc ∫⁻ y in Set.Ico 0 w, ENNReal.ofReal (w - y) ∂(renewalMeasure ρ)
        = ∫⁻ y in Set.Ico 0 w, ((volume : Measure ℝ).restrict (Set.Ico 0 w))
            (Prod.mk y ⁻¹' {q : ℝ × ℝ | q.1 < w - q.2}) ∂(renewalMeasure ρ) := by
          refine setLIntegral_congr_fun measurableSet_Ico fun y hy => ?_
          have e : Prod.mk y ⁻¹' {q : ℝ × ℝ | q.1 < w - q.2} = Set.Iio (w - y) := by
            ext t
            simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Iio]
            constructor <;> intro h <;> linarith
          have e2 : Set.Iio (w - y) ∩ Set.Ico 0 w = Set.Ico 0 (w - y) := by
            ext t
            simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ico]
            constructor
            · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
            · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith [hy.1]⟩
          rw [e, Measure.restrict_apply measurableSet_Iio, e2, Real.volume_Ico, sub_zero]
      _ = ∫⁻ t in Set.Ico 0 w, ((renewalMeasure ρ).restrict (Set.Ico 0 w))
            ((fun y => (y, t)) ⁻¹' {q : ℝ × ℝ | q.1 < w - q.2}) := swap_count _ _ _ hS2
      _ = ∫⁻ t in Set.Ico 0 w, renewalMeasure ρ (Set.Ico 0 (w - t)) := by
          refine setLIntegral_congr_fun measurableSet_Ico fun t ht => ?_
          have e : (fun y => (y, t)) ⁻¹' {q : ℝ × ℝ | q.1 < w - q.2} = Set.Iio (w - t) := by
            ext y; simp
          have e2 : Set.Iio (w - t) ∩ Set.Ico 0 w = Set.Ico 0 (w - t) := by
            ext y
            simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ico]
            constructor
            · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
            · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith [ht.1]⟩
          rw [e, Measure.restrict_apply measurableSet_Iio, e2]
  -- the interval bound gives `∫_0^w U[t,w) dt ≤ ∫_0^w M(w - t) dt`
  have hle : ∫⁻ y in Set.Ico 0 w, ENNReal.ofReal y ∂(renewalMeasure ρ)
      ≤ ∫⁻ y in Set.Ico 0 w, ENNReal.ofReal (w - y) ∂(renewalMeasure ρ) := by
    rw [hI, hK]
    refine setLIntegral_mono' measurableSet_Ico fun t ht => ?_
    have := renewal_interval_bound ρ t (w - t) ht.1
    rwa [show t + (w - t) = w by ring] at this
  -- the two integrals add up to `w M(w)`
  have hsum : ∫⁻ y in Set.Ico 0 w, ENNReal.ofReal y ∂(renewalMeasure ρ)
      + ∫⁻ y in Set.Ico 0 w, ENNReal.ofReal (w - y) ∂(renewalMeasure ρ)
      = ENNReal.ofReal w * renewalMeasure ρ (Set.Ico 0 w) := by
    rw [← lintegral_add_left ENNReal.measurable_ofReal, ← setLIntegral_const]
    refine setLIntegral_congr_fun measurableSet_Ico fun y hy => ?_
    rw [← ENNReal.ofReal_add hy.1 (by linarith [hy.2]), add_sub_cancel]
  -- conclude: `2 I ≤ w M(w)`
  have hsplit : ENNReal.ofReal w * renewalMeasure ρ (Set.Ico 0 w)
      = ENNReal.ofReal (w / 2) * renewalMeasure ρ (Set.Ico 0 w)
        + ENNReal.ofReal (w / 2) * renewalMeasure ρ (Set.Ico 0 w) := by
    rw [← add_mul, ← ENNReal.ofReal_add (by linarith) (by linarith), add_halves]
  by_contra hcon
  have hlt := not_le.1 hcon
  have h2 := ENNReal.add_lt_add hlt hlt
  rw [← hsplit, ← hsum] at h2
  exact absurd (add_le_add le_rfl hle) (not_le.2 h2)
