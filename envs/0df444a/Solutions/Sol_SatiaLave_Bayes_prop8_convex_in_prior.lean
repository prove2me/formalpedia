-- Prove2me | solution 1 for SatiaLave.Bayes.prop8_convex_in_prior
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T14:12:50.429967+00:00
-- url     : https://prove2.me/submissions/cb27a9ed-dc53-460a-9872-2717082b1682

import Mathlib
import Definitions.Def_SatiaLave_Bayes_Model

set_option autoImplicit false

open MeasureTheory

namespace SatiaLave.Bayes.P8

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
  {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
  {g g₁ g₂ : Measure (Mat S D)} {t : ℝ}

lemma meas_coord (l : S) (m : D l) (j : S) : Measurable (fun P : Mat S D => P l m j) := by
  fun_prop

lemma ae_stoch (hg : IsPrior g) : ∀ᵐ P ∂g, IsStoch P := by
  rw [ae_iff]; exact hg.2

lemma coord_nonneg_le {P : Mat S D} (hP : IsStoch P) (l : S) (m : D l) (j : S) :
    0 ≤ P l m j ∧ P l m j ≤ 1 := by
  have h := hP l m
  refine ⟨h.1 j, ?_⟩
  rw [← h.2]
  exact Finset.single_le_sum (fun x _ => h.1 x) (Finset.mem_univ j)

lemma integrable_coord (hg : IsPrior g) (l : S) (m : D l) (j : S) :
    Integrable (fun P : Mat S D => P l m j) g := by
  haveI := hg.1
  refine (integrable_const (1:ℝ)).mono' (meas_coord l m j).aestronglyMeasurable ?_
  filter_upwards [ae_stoch hg] with P hP
  have := coord_nonneg_le hP l m j
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]

lemma coord_ae_nonneg (hg : IsPrior g) (l : S) (m : D l) (j : S) :
    0 ≤ᵐ[g] fun P : Mat S D => P l m j := by
  filter_upwards [ae_stoch hg] with P hP using (coord_nonneg_le hP l m j).1

lemma pbar_nonneg (hg : IsPrior g) (l : S) (m : D l) (j : S) : 0 ≤ pbar g l m j :=
  integral_nonneg_of_ae (coord_ae_nonneg hg l m j)

lemma sum_pbar (hg : IsPrior g) (i : S) (k : D i) : ∑ j, pbar g i k j = 1 := by
  haveI := hg.1
  unfold pbar
  rw [← integral_finsetSum _ (fun j _ => integrable_coord hg i k j)]
  rw [integral_congr_ae (g := fun _ => (1:ℝ))]
  · simp
  · filter_upwards [ae_stoch hg] with P hP using (hP i k).2

lemma lintegral_coord (hg : IsPrior g) (l : S) (m : D l) (j : S) :
    ∫⁻ P, ENNReal.ofReal (P l m j) ∂g = ENNReal.ofReal (pbar g l m j) :=
  (ofReal_integral_eq_lintegral_ofReal (integrable_coord hg l m j)
    (coord_ae_nonneg hg l m j)).symm

lemma withDensity_eq (hg : IsPrior g) (l : S) (m : D l) (j : S) :
    g.withDensity (fun P => ENNReal.ofReal (P l m j)) =
      ENNReal.ofReal (pbar g l m j) • bayes g l m j := by
  unfold bayes
  split_ifs with h
  · rw [h, ENNReal.ofReal_zero, zero_smul]
    apply Measure.measure_univ_eq_zero.mp
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_coord hg, h,
      ENNReal.ofReal_zero]
  · have hp : 0 < pbar g l m j := lt_of_le_of_ne (pbar_nonneg hg l m j) (Ne.symm h)
    rw [smul_smul, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top,
      one_smul]

lemma bayes_prior (hg : IsPrior g) (l : S) (m : D l) (j : S) : IsPrior (bayes g l m j) := by
  by_cases h : pbar g l m j = 0
  · unfold bayes; rw [if_pos h]; exact hg
  · have hp : 0 < pbar g l m j := lt_of_le_of_ne (pbar_nonneg hg l m j) (Ne.symm h)
    have hb : bayes g l m j = (ENNReal.ofReal (pbar g l m j))⁻¹ •
        g.withDensity (fun P => ENNReal.ofReal (P l m j)) := by
      unfold bayes; rw [if_neg h]
    rw [hb]
    refine ⟨⟨?_⟩, ?_⟩
    · rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        lintegral_coord hg, smul_eq_mul,
        ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top]
    · rw [Measure.smul_apply, withDensity_absolutelyContinuous _ _ hg.2, smul_zero]

lemma mix_prior (hg₁ : IsPrior g₁) (hg₂ : IsPrior g₂) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    IsPrior (ENNReal.ofReal t • g₁ + ENNReal.ofReal (1 - t) • g₂) := by
  haveI := hg₁.1; haveI := hg₂.1
  refine ⟨⟨?_⟩, ?_⟩
  · simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add ht₀ (by linarith)]; simp
  · simp only [Measure.add_apply, Measure.smul_apply, hg₁.2, hg₂.2, smul_eq_mul, mul_zero,
      add_zero]

lemma pbar_mix (hg₁ : IsPrior g₁) (hg₂ : IsPrior g₂) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (l : S) (m : D l) (j : S) :
    pbar (ENNReal.ofReal t • g₁ + ENNReal.ofReal (1 - t) • g₂) l m j =
      t * pbar g₁ l m j + (1 - t) * pbar g₂ l m j := by
  unfold pbar
  rw [integral_add_measure ((integrable_coord hg₁ l m j).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_coord hg₂ l m j).smul_measure ENNReal.ofReal_ne_top), integral_smul_measure,
    integral_smul_measure, ENNReal.toReal_ofReal ht₀, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, smul_eq_mul]

lemma step_j (f : S → Measure (Mat S D) → ℝ) (Δ : ℝ)
    (hΔ : ∀ (j : S) (h₁ h₂ : Measure (Mat S D)) (s : ℝ), IsPrior h₁ → IsPrior h₂ → 0 ≤ s →
      s ≤ 1 → f j (ENNReal.ofReal s • h₁ + ENNReal.ofReal (1 - s) • h₂) - s * f j h₁ -
        (1 - s) * f j h₂ ≤ Δ)
    (hg₁ : IsPrior g₁) (hg₂ : IsPrior g₂) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (l : S) (m : D l) (j : S) :
    pbar (ENNReal.ofReal t • g₁ + ENNReal.ofReal (1 - t) • g₂) l m j *
        f j (bayes (ENNReal.ofReal t • g₁ + ENNReal.ofReal (1 - t) • g₂) l m j) ≤
      t * (pbar g₁ l m j * f j (bayes g₁ l m j)) +
        (1 - t) * (pbar g₂ l m j * f j (bayes g₂ l m j)) +
        pbar (ENNReal.ofReal t • g₁ + ENNReal.ofReal (1 - t) • g₂) l m j * Δ := by
  have hmix := mix_prior hg₁ hg₂ ht₀ ht₁
  have hW := withDensity_eq hmix l m j
  have hp := pbar_mix hg₁ hg₂ ht₀ ht₁ l m j
  have ha0 : 0 ≤ pbar g₁ l m j := pbar_nonneg hg₁ l m j
  have hb0 : 0 ≤ pbar g₂ l m j := pbar_nonneg hg₂ l m j
  have h1t : 0 ≤ 1 - t := by linarith
  rw [hp] at hW ⊢
  rcases eq_or_lt_of_le (show 0 ≤ t * pbar g₁ l m j + (1 - t) * pbar g₂ l m j by positivity)
    with h0 | hpos
  · have e1 : t * pbar g₁ l m j = 0 := by
      nlinarith [mul_nonneg ht₀ ha0, mul_nonneg h1t hb0]
    have e2 : (1 - t) * pbar g₂ l m j = 0 := by
      nlinarith [mul_nonneg ht₀ ha0, mul_nonneg h1t hb0]
    rw [← h0, ← mul_assoc, e1, ← mul_assoc, e2]; simp
  · set a := pbar g₁ l m j with ha
    set b := pbar g₂ l m j with hb
    set p := t * a + (1 - t) * b with hpdef
    have hbm : bayes (ENNReal.ofReal t • g₁ + ENNReal.ofReal (1 - t) • g₂) l m j =
        ENNReal.ofReal (t * a / p) • bayes g₁ l m j +
          ENNReal.ofReal (1 - t * a / p) • bayes g₂ l m j := by
      have e : bayes (ENNReal.ofReal t • g₁ + ENNReal.ofReal (1 - t) • g₂) l m j =
          (ENNReal.ofReal p)⁻¹ • (ENNReal.ofReal t • g₁ + ENNReal.ofReal (1 - t) • g₂).withDensity
            (fun P => ENNReal.ofReal (P l m j)) := by
        rw [hW, smul_smul,
          ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hpos).ne' ENNReal.ofReal_ne_top, one_smul]
      rw [e, withDensity_add_measure, withDensity_smul_measure, withDensity_smul_measure,
        withDensity_eq hg₁, withDensity_eq hg₂, smul_add, smul_smul, smul_smul, smul_smul,
        smul_smul, ← ENNReal.ofReal_inv_of_pos hpos,
        ← ENNReal.ofReal_mul (inv_nonneg.2 hpos.le), ← ENNReal.ofReal_mul (inv_nonneg.2 hpos.le),
        ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 hpos.le) ht₀),
        ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 hpos.le) h1t)]
      simp only [← ha, ← hb]
      have hp0 : p ≠ 0 := hpos.ne'
      congr 3
      · rw [div_eq_inv_mul]; ring
      · field_simp
        try (rw [hpdef]; ring)
    have hs0 : 0 ≤ t * a / p := div_nonneg (mul_nonneg ht₀ ha0) hpos.le
    have hs1 : t * a / p ≤ 1 := by
      rw [div_le_one hpos]; nlinarith [mul_nonneg h1t hb0]
    have hΔ' := hΔ j _ _ _ (bayes_prior hg₁ l m j) (bayes_prior hg₂ l m j) hs0 hs1
    rw [← hbm] at hΔ'
    have h3 := mul_le_mul_of_nonneg_left hΔ' hpos.le
    have e : p * (f j (bayes (ENNReal.ofReal t • g₁ + ENNReal.ofReal (1 - t) • g₂) l m j) -
        t * a / p * f j (bayes g₁ l m j) - (1 - t * a / p) * f j (bayes g₂ l m j)) =
        p * f j (bayes (ENNReal.ofReal t • g₁ + ENNReal.ofReal (1 - t) • g₂) l m j) -
          (t * a) * f j (bayes g₁ l m j) - ((1 - t) * b) * f j (bayes g₂ l m j) := by
      have hp0 : p ≠ 0 := hpos.ne'
      field_simp
      try (rw [hpdef]; ring)
    rw [e] at h3
    linarith

lemma step (M : UncertainMDP S D) (f : S → Measure (Mat S D) → ℝ) (hf : SolvesEq10 M f)
    (Δ : ℝ)
    (hΔ : ∀ (j : S) (h₁ h₂ : Measure (Mat S D)) (s : ℝ), IsPrior h₁ → IsPrior h₂ → 0 ≤ s →
      s ≤ 1 → f j (ENNReal.ofReal s • h₁ + ENNReal.ofReal (1 - s) • h₂) - s * f j h₁ -
        (1 - s) * f j h₂ ≤ Δ)
    (hg₁ : IsPrior g₁) (hg₂ : IsPrior g₂) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (i : S) :
    f i (ENNReal.ofReal t • g₁ + ENNReal.ofReal (1 - t) • g₂) ≤
      t * f i g₁ + (1 - t) * f i g₂ + M.β * Δ := by
  have hmix := mix_prior hg₁ hg₂ ht₀ ht₁
  rw [hf i _ hmix]
  refine Finset.sup'_le _ _ (fun k _ => ?_)
  have h1 : ∑ j, pbar g₁ i k j * M.r i k j + M.β * ∑ j, pbar g₁ i k j * f j (bayes g₁ i k j)
      ≤ f i g₁ := by
    rw [hf i g₁ hg₁]
    exact Finset.le_sup' (fun k : D i => ∑ j, pbar g₁ i k j * M.r i k j +
      M.β * ∑ j, pbar g₁ i k j * f j (bayes g₁ i k j)) (Finset.mem_univ k)
  have h2 : ∑ j, pbar g₂ i k j * M.r i k j + M.β * ∑ j, pbar g₂ i k j * f j (bayes g₂ i k j)
      ≤ f i g₂ := by
    rw [hf i g₂ hg₂]
    exact Finset.le_sup' (fun k : D i => ∑ j, pbar g₂ i k j * M.r i k j +
      M.β * ∑ j, pbar g₂ i k j * f j (bayes g₂ i k j)) (Finset.mem_univ k)
  have hr : ∑ j, pbar (ENNReal.ofReal t • g₁ + ENNReal.ofReal (1 - t) • g₂) i k j * M.r i k j =
      t * ∑ j, pbar g₁ i k j * M.r i k j + (1 - t) * ∑ j, pbar g₂ i k j * M.r i k j := by
    simp only [pbar_mix hg₁ hg₂ ht₀ ht₁, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hfj : ∑ j, pbar (ENNReal.ofReal t • g₁ + ENNReal.ofReal (1 - t) • g₂) i k j *
        f j (bayes (ENNReal.ofReal t • g₁ + ENNReal.ofReal (1 - t) • g₂) i k j) ≤
      t * ∑ j, pbar g₁ i k j * f j (bayes g₁ i k j) +
        (1 - t) * ∑ j, pbar g₂ i k j * f j (bayes g₂ i k j) + Δ := by
    calc _ ≤ ∑ j, (t * (pbar g₁ i k j * f j (bayes g₁ i k j)) +
            (1 - t) * (pbar g₂ i k j * f j (bayes g₂ i k j)) +
            pbar (ENNReal.ofReal t • g₁ + ENNReal.ofReal (1 - t) • g₂) i k j * Δ) :=
          Finset.sum_le_sum (fun j _ => step_j f Δ hΔ hg₁ hg₂ ht₀ ht₁ i k j)
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← Finset.sum_mul, sum_pbar hmix i k, one_mul]
  have hβ := M.β_nonneg
  rw [hr]
  nlinarith [mul_le_mul_of_nonneg_left hfj hβ, mul_le_mul_of_nonneg_left h1 ht₀,
    mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 ht₁)]

end SatiaLave.Bayes.P8

open MeasureTheory SatiaLave.Bayes in
theorem solution {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D)
    (f : S → Measure (Mat S D) → ℝ) (hf : SolvesEq10 M f) (hb : IsBoundedOnPriors f)
    (g₁ g₂ : Measure (Mat S D)) (hg₁ : IsPrior g₁) (hg₂ : IsPrior g₂)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (i : S) :
    f i (ENNReal.ofReal t • g₁ + ENNReal.ofReal (1 - t) • g₂) ≤
      t * f i g₁ + (1 - t) * f i g₂ := by
  obtain ⟨C, hC⟩ := hb
  let A : Set ℝ := {x | ∃ (j : S) (h₁ h₂ : Measure (Mat S D)) (s : ℝ), IsPrior h₁ ∧
    IsPrior h₂ ∧ 0 ≤ s ∧ s ≤ 1 ∧ x = f j (ENNReal.ofReal s • h₁ + ENNReal.ofReal (1 - s) • h₂) -
      s * f j h₁ - (1 - s) * f j h₂}
  have hmem : ∀ (j : S) (h₁ h₂ : Measure (Mat S D)) (s : ℝ), IsPrior h₁ → IsPrior h₂ → 0 ≤ s →
      s ≤ 1 → f j (ENNReal.ofReal s • h₁ + ENNReal.ofReal (1 - s) • h₂) - s * f j h₁ -
        (1 - s) * f j h₂ ∈ A :=
    fun j h₁ h₂ s a b c d => ⟨j, h₁, h₂, s, a, b, c, d, rfl⟩
  have hne : A.Nonempty := ⟨_, hmem i g₁ g₂ t hg₁ hg₂ ht₀ ht₁⟩
  have hbdd : BddAbove A := by
    refine ⟨3 * C, ?_⟩
    rintro x ⟨j, h₁, h₂, s, p₁, p₂, s0, s1, rfl⟩
    have a1 := abs_le.1 (hC j _ (P8.mix_prior p₁ p₂ s0 s1))
    have a2 := abs_le.1 (hC j h₁ p₁)
    have a3 := abs_le.1 (hC j h₂ p₂)
    have hs1 : 0 ≤ 1 - s := by linarith
    nlinarith [mul_le_mul_of_nonneg_left a2.1 s0, mul_le_mul_of_nonneg_left a3.1 hs1]
  have hle : ∀ (j : S) (h₁ h₂ : Measure (Mat S D)) (s : ℝ), IsPrior h₁ → IsPrior h₂ → 0 ≤ s →
      s ≤ 1 → f j (ENNReal.ofReal s • h₁ + ENNReal.ofReal (1 - s) • h₂) - s * f j h₁ -
        (1 - s) * f j h₂ ≤ sSup A :=
    fun j h₁ h₂ s a b c d => le_csSup hbdd (hmem j h₁ h₂ s a b c d)
  have key : ∀ x ∈ A, x ≤ M.β * sSup A := by
    rintro x ⟨j, h₁, h₂, s, p₁, p₂, s0, s1, rfl⟩
    have := P8.step M f hf (sSup A) hle p₁ p₂ s0 s1 j
    linarith
  have hΔ : sSup A ≤ M.β * sSup A := csSup_le hne key
  have hΔ0 : sSup A ≤ 0 := by nlinarith [M.β_lt_one]
  have := hle i g₁ g₂ t hg₁ hg₂ ht₀ ht₁
  linarith
