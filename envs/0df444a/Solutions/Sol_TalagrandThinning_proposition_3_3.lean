-- Prove2me | solution 1 for TalagrandThinning.proposition_3_3
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T06:48:37.854001+00:00
-- url     : https://prove2.me/submissions/5d2077b9-8ed5-4004-8f8d-0a0aa4f698c2

import Mathlib
import Definitions.Def_TalagrandThinning_liftL
import Theorems.Thm_TalagrandThinning_lemma_3_1
import Theorems.Thm_TalagrandThinning_lemma_3_2

set_option autoImplicit false

open MeasureTheory

namespace TTP33
open TalagrandThinning

lemma weight_nonneg {N : ℕ} (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) (x : Cube N) :
    0 ≤ weight s x :=
  Finset.prod_nonneg fun i _ => by split_ifs <;> linarith

lemma prodLaw_apply {N : ℕ} (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) (S : Set (Cube N)) :
    prodLaw N s S = ENNReal.ofReal (∑ x, weight s x * S.indicator (fun _ => (1 : ℝ)) x) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (weight_nonneg s h0 h1 x)
    (Set.indicator_nonneg (fun _ _ => zero_le_one) x))]
  simp only [prodLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Measure.dirac_apply' _ (Set.toFinite S).measurableSet]
  by_cases hx : x ∈ S <;> simp [hx, Set.indicator]

end TTP33

open TalagrandThinning in
theorem solution {N : ℕ} (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (U : Set (Cube N)) (hU : IsUpperSet U) :
    (∀ I : Finset (Fin N), 0 ≤ (t * (1 - p) / (p * (1 - t))) ^ I.card *
        TalagrandThinning.fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2) ∧
    (∀ j : Cube N, prodLaw N t {x : Cube N | j ⊓ x ∈ U} ≤
      ENNReal.ofReal (∑ I ∈ (Finset.univ.filter (fun i => j i = true)).powerset,
        (t * (1 - p) / (p * (1 - t))) ^ I.card *
          TalagrandThinning.fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2)) := by
  have hr : 0 ≤ t * (1 - p) / (p * (1 - t)) := by
    apply div_nonneg <;> apply mul_nonneg <;> linarith
  refine ⟨fun I => mul_nonneg (pow_nonneg hr _) (sq_nonneg _), fun j => ?_⟩
  rw [TTP33.prodLaw_apply t ht0.le ht1.le]
  apply ENNReal.ofReal_le_ofReal
  set f : Cube N → ℝ := U.indicator (fun _ => (1 : ℝ))
  have key := (lemma_3_2 t p ht0 ht1 hp0 hp1 f j).2
  have hb : ∀ I : Finset (Fin N), beta t p ^ (2 * I.card) = (t * (1 - p) / (p * (1 - t))) ^ I.card := by
    intro I
    rw [pow_mul, beta, Real.sq_sqrt hr]
  simp only [hb] at key
  rw [← key, expect]
  refine Finset.sum_le_sum fun x _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (TTP33.weight_nonneg t ht0.le ht1.le x)
  have := lemma_3_1 t p ht0 ht1 hp0 hp1 U hU j x
  simpa [Set.indicator, f] using this
