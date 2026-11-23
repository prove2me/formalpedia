-- Prove2me | solution 1 for TalagrandThinning.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T06:54:59.991474+00:00
-- url     : https://prove2.me/submissions/359e141c-fdc4-46e7-96bf-0c2474184f70

import Mathlib
import Definitions.Def_TalagrandThinning_IsSpread
import Definitions.Def_TalagrandThinning_retention
import Definitions.Def_TalagrandThinning_StochDomSubset
import Theorems.Thm_TalagrandThinning_upset_bound_eq_4_1
import Theorems.Thm_StochIneqPO_Comparison_theorem1_tfae

set_option autoImplicit false

open MeasureTheory

namespace TTT12

open TalagrandThinning

/-- `µ_s` is a probability measure for `0 ≤ s ≤ 1`. -/
theorem prodLaw_isProbabilityMeasure (N : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IsProbabilityMeasure (prodLaw N s) := by
  constructor
  have hw : ∀ x : Cube N, 0 ≤ weight s x := fun x =>
    Finset.prod_nonneg fun i _ => by split_ifs <;> linarith
  have hsum : ∑ x : Cube N, weight s x = 1 := by
    unfold weight
    rw [← Fintype.prod_sum (fun (i : Fin N) (b : Bool) => if b then s else 1 - s)]
    simp
  simp only [prodLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hw x), hsum, ENNReal.ofReal_one]

theorem retention_isProbabilityMeasure {N : ℕ} (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ν : Measure (Cube N)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (retention t ν) := by
  have := prodLaw_isProbabilityMeasure N t ht0 ht1
  unfold retention
  exact Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

theorem part1 {N : ℕ} (t q : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (ν : Measure (Cube N)) [IsProbabilityMeasure ν] (hν : IsSpread q ν)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hη : t * q * (1 - p) / (p * (1 - t)) ≤ 1) :
    StochDomSubset (retention t ν) (prodLaw N p) := by
  have := prodLaw_isProbabilityMeasure N p hp0.le hp1.le
  have := retention_isProbabilityMeasure t ht0.le ht1.le ν
  have h := (StochIneqPO.Comparison.theorem1_tfae (retention t ν) (prodLaw N p)).out 5 1
  exact h.mp fun B _ hB =>
    (upset_bound_eq_4_1 t q p ht0 ht1 hq0 hq1 hp0 hp1 ν hν hη B hB).2.2.2.2.2.2

end TTT12

open TalagrandThinning in
theorem solution {N : ℕ} (t q : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (ν : Measure (Cube N)) [IsProbabilityMeasure ν] (hν : IsSpread q ν) :
    (∀ p : ℝ, 0 < p → p < 1 → t * q * (1 - p) / (p * (1 - t)) ≤ 1 →
      StochDomSubset (retention t ν) (prodLaw N p)) ∧
    StochDomSubset (retention t ν) (prodLaw N (t * q / (1 - t + t * q))) := by
  refine ⟨fun p hp0 hp1 hη => TTT12.part1 t q ht0 ht1 hq0 hq1 ν hν p hp0 hp1 hη, ?_⟩
  have hD : 0 < 1 - t + t * q := by nlinarith
  have htq : 0 < t * q := mul_pos ht0 hq0
  have h1t : 0 < 1 - t := by linarith
  apply TTT12.part1 t q ht0 ht1 hq0 hq1 ν hν
  · exact div_pos htq hD
  · rw [div_lt_one hD]; linarith
  · have hp : 1 - t * q / (1 - t + t * q) = (1 - t) / (1 - t + t * q) := by
      field_simp; ring
    rw [hp, div_le_one (by positivity)]
    apply le_of_eq
    field_simp
