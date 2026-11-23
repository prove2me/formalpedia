-- Prove2me | solution 1 for TalagrandThinning.upset_bound_eq_4_1
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T06:50:35.530799+00:00
-- url     : https://prove2.me/submissions/c3af33cf-b2a7-48c6-80e3-315da6087d83

import Mathlib
import Definitions.Def_TalagrandThinning_liftL
import Definitions.Def_TalagrandThinning_IsSpread
import Definitions.Def_TalagrandThinning_retention
import Theorems.Thm_TalagrandThinning_proposition_3_3
import Theorems.Thm_TalagrandThinning_fourier_basis_eq_2_1

set_option autoImplicit false

open MeasureTheory

namespace TTUpset

open TalagrandThinning

lemma weight_nonneg {N : ℕ} (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : Cube N) :
    0 ≤ weight s x := by
  unfold weight
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith

lemma prodLaw_apply {N : ℕ} (s : ℝ) (S : Set (Cube N)) :
    prodLaw N s S = ∑ x : Cube N, ENNReal.ofReal (weight s x) * S.indicator 1 x := by
  unfold prodLaw
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]

instance prodLaw_finite {N : ℕ} (s : ℝ) : IsFiniteMeasure (prodLaw N s) := by
  constructor
  rw [prodLaw_apply]
  refine ENNReal.sum_lt_top.2 fun x _ => ?_
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  by_cases h : x ∈ (Set.univ : Set (Cube N)) <;> simp [h]

open Classical in
lemma measure_eq_sum {N : ℕ} (μ : Measure (Cube N)) (S : Set (Cube N)) :
    μ S = ∑ J : Cube N, if J ∈ S then μ {J} else 0 := by
  classical
  rw [← Finset.sum_filter, MeasureTheory.sum_measure_singleton]
  congr 1
  ext J; simp

lemma retention_eq {N : ℕ} (t : ℝ) (ν : Measure (Cube N)) (U : Set (Cube N)) :
    retention t ν U = ∑ J : Cube N, ν {J} * prodLaw N t {x | J ⊓ x ∈ U} := by
  unfold retention
  rw [Measure.map_apply (measurable_of_finite _) (Set.toFinite U).measurableSet,
    Measure.prod_apply (Set.toFinite _).measurableSet, lintegral_fintype]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [mul_comm]
  rfl

lemma beta_sq (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    beta t p ^ 2 = t * (1 - p) / (p * (1 - t)) := by
  unfold beta
  rw [Real.sq_sqrt]
  apply div_nonneg <;> apply mul_nonneg <;> linarith

end TTUpset

open TalagrandThinning TTUpset in
theorem solution {N : ℕ} (t q p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hp0 : 0 < p) (hp1 : p < 1) (ν : Measure (Cube N)) [IsProbabilityMeasure ν]
    (hν : IsSpread q ν) (hη : t * q * (1 - p) / (p * (1 - t)) ≤ 1)
    (U : Set (Cube N)) (hU : IsUpperSet U) :
    retention t ν U ≤ ENNReal.ofReal (∑ J : Cube N, (ν {J}).toReal *
        ∑ I ∈ (Finset.univ.filter (fun i => J i = true)).powerset,
          beta t p ^ (2 * I.card) * TalagrandThinning.fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2) ∧
    (∑ J : Cube N, (ν {J}).toReal *
        ∑ I ∈ (Finset.univ.filter (fun i => J i = true)).powerset,
          beta t p ^ (2 * I.card) * TalagrandThinning.fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2) =
      ∑ I : Finset (Fin N), beta t p ^ (2 * I.card) *
        TalagrandThinning.fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2 *
          (ν {J : Cube N | ∀ i ∈ I, J i = true}).toReal ∧
    (∑ I : Finset (Fin N), beta t p ^ (2 * I.card) *
        TalagrandThinning.fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2 *
          (ν {J : Cube N | ∀ i ∈ I, J i = true}).toReal) ≤
      ∑ I : Finset (Fin N),
        (beta t p ^ 2 * q) ^ I.card * TalagrandThinning.fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2 ∧
    (∑ I : Finset (Fin N),
        (beta t p ^ 2 * q) ^ I.card * TalagrandThinning.fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2) ≤
      ∑ I : Finset (Fin N), TalagrandThinning.fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2 ∧
    ∑ I : Finset (Fin N), TalagrandThinning.fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2 =
      expect p (fun x => U.indicator (fun _ => (1 : ℝ)) x ^ 2) ∧
    expect p (fun x => U.indicator (fun _ => (1 : ℝ)) x ^ 2) = (prodLaw N p U).toReal ∧
    retention t ν U ≤ prodLaw N p U := by
  classical
  set f := U.indicator (fun _ => (1 : ℝ)) with hf
  set a : Finset (Fin N) → ℝ := fun I => beta t p ^ (2 * I.card) *
    TalagrandThinning.fourierCoeff p f I ^ 2 with ha
  have hb := beta_sq t p ht0 ht1 hp0 hp1
  have ha' : ∀ I : Finset (Fin N), a I = (t * (1 - p) / (p * (1 - t))) ^ I.card *
      TalagrandThinning.fourierCoeff p f I ^ 2 := by
    intro I; simp only [ha]; rw [pow_mul, hb]
  obtain ⟨hpos, hbound⟩ := proposition_3_3 t p ht0 ht1 hp0 hp1 U hU
  have ha0 : ∀ I, 0 ≤ a I := fun I => by rw [ha']; exact hpos I
  -- step 1
  have h1 : retention t ν U ≤ ENNReal.ofReal (∑ J : Cube N, (ν {J}).toReal *
      ∑ I ∈ (Finset.univ.filter (fun i => J i = true)).powerset, a I) := by
    rw [retention_eq, ENNReal.ofReal_sum_of_nonneg (fun J _ => mul_nonneg ENNReal.toReal_nonneg
      (Finset.sum_nonneg fun I _ => ha0 I))]
    refine Finset.sum_le_sum fun J _ => ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    refine mul_le_mul_right ?_ _
    refine (hbound J).trans (le_of_eq ?_)
    congr 1
    exact Finset.sum_congr rfl fun I _ => (ha' I).symm
  -- step 2
  have h2 : (∑ J : Cube N, (ν {J}).toReal *
      ∑ I ∈ (Finset.univ.filter (fun i => J i = true)).powerset, a I) =
      ∑ I : Finset (Fin N), a I * (ν {J : Cube N | ∀ i ∈ I, J i = true}).toReal := by
    have hps : ∀ J : Cube N, (Finset.univ.filter (fun i => J i = true)).powerset =
        Finset.univ.filter (fun I : Finset (Fin N) => ∀ i ∈ I, J i = true) := by
      intro J; ext I; simp [Finset.subset_iff]
    simp_rw [hps, Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [measure_eq_sum ν, ENNReal.toReal_sum (fun J _ => by split_ifs <;> simp [measure_ne_top]),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    by_cases h : ∀ i ∈ I, J i = true
    · rw [if_pos (show J ∈ {J : Cube N | ∀ i ∈ I, J i = true} from h), mul_comm, if_pos h]
    · simp [h]
  -- step 3
  have h3 : (∑ I : Finset (Fin N), a I * (ν {J : Cube N | ∀ i ∈ I, J i = true}).toReal) ≤
      ∑ I : Finset (Fin N), (beta t p ^ 2 * q) ^ I.card *
        TalagrandThinning.fourierCoeff p f I ^ 2 := by
    refine Finset.sum_le_sum fun I _ => ?_
    have hle : (ν {J : Cube N | ∀ i ∈ I, J i = true}).toReal ≤ q ^ I.card :=
      ENNReal.toReal_le_of_le_ofReal (pow_nonneg hq0.le _) (hν I)
    calc a I * (ν {J : Cube N | ∀ i ∈ I, J i = true}).toReal ≤ a I * q ^ I.card :=
          mul_le_mul_of_nonneg_left hle (ha0 I)
      _ = _ := by simp only [ha]; rw [pow_mul, mul_pow]; ring
  -- step 4
  have hη' : beta t p ^ 2 * q = t * q * (1 - p) / (p * (1 - t)) := by rw [hb]; ring
  have hη0 : 0 ≤ beta t p ^ 2 * q := by positivity
  have h4 : (∑ I : Finset (Fin N), (beta t p ^ 2 * q) ^ I.card *
        TalagrandThinning.fourierCoeff p f I ^ 2) ≤
      ∑ I : Finset (Fin N), TalagrandThinning.fourierCoeff p f I ^ 2 := by
    refine Finset.sum_le_sum fun I _ => ?_
    exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hη0 (hη' ▸ hη))
  -- step 5
  have h5 : ∑ I : Finset (Fin N), TalagrandThinning.fourierCoeff p f I ^ 2 =
      expect p (fun x => f x ^ 2) :=
    ((fourier_basis_eq_2_1 (N := N) p hp0 hp1).2.2.2.2 f).symm
  -- step 6
  have h6 : expect p (fun x => f x ^ 2) = (prodLaw N p U).toReal := by
    rw [prodLaw_apply, ENNReal.toReal_sum (fun x _ => by
      by_cases h : x ∈ U <;> simp [h])]
    unfold expect
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (weight_nonneg p hp0.le hp1.le x)]
    by_cases h : x ∈ U <;> simp [hf, h]
  refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
  calc retention t ν U ≤ _ := h1
    _ ≤ ENNReal.ofReal (prodLaw N p U).toReal := by
        apply ENNReal.ofReal_le_ofReal
        rw [h2, ← h6, ← h5]
        exact h3.trans h4
    _ = prodLaw N p U := ENNReal.ofReal_toReal (measure_ne_top _ _)
