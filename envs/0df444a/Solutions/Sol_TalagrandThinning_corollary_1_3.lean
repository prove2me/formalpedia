-- Prove2me | solution 1 for TalagrandThinning.corollary_1_3
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T08:52:52.951379+00:00
-- url     : https://prove2.me/submissions/b8058e02-a4b6-4252-a55b-37c8da31a9b2

import Mathlib
import Definitions.Def_TalagrandThinning_IsSpread
import Definitions.Def_TalagrandThinning_retention
import Definitions.Def_TalagrandThinning_StochDomSubset
import Theorems.Thm_TalagrandThinning_theorem_1_2

set_option autoImplicit false

open MeasureTheory

namespace TTC13

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

/-- On a finite discrete space, a measure is the sum of its point masses. -/
theorem meas_eq_sum {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) (S : Set α) [DecidablePred (· ∈ S)] :
    μ S = ∑ a ∈ Finset.univ.filter (· ∈ S), μ {a} := by
  rw [sum_measure_singleton]; congr 1; ext a; simp

/-- Gluing: a coupling of the retained set with `µ_p` lifts to the pair `(J, X_α)`. -/
theorem glue {N : ℕ} (Q σ : Measure (Cube N × Cube N)) [IsFiniteMeasure Q]
    (μ : Measure (Cube N))
    (hσ0 : σ {z : Cube N × Cube N | z.1 ≤ z.2}ᶜ = 0)
    (hσ1 : σ.map Prod.fst = Q.map (fun z : Cube N × Cube N => z.1 ⊓ z.2))
    (hσ2 : σ.map Prod.snd = μ) :
    ∃ π : Measure (Cube N × Cube N × Cube N),
      π.map (fun z : Cube N × Cube N × Cube N => (z.1, z.2.1)) = Q ∧
      π.map (fun z : Cube N × Cube N × Cube N => z.2.2) = μ ∧
      π {z : Cube N × Cube N × Cube N | z.1 ⊓ z.2.1 ≤ z.2.2}ᶜ = 0 := by
  classical
  set r := Q.map (fun z : Cube N × Cube N => z.1 ⊓ z.2) with hr
  have hrs : ∀ s, r {s} = ∑ a ∈ Finset.univ.filter (fun a : Cube N × Cube N => a.1 ⊓ a.2 = s),
      Q {a} := by
    intro s
    rw [hr, Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _), meas_eq_sum]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext a; simp
  have hσs : ∀ s, ∑ y, σ {(s, y)} = r {s} := by
    intro s
    rw [← hσ1, Measure.map_apply measurable_fst (measurableSet_singleton _), meas_eq_sum]
    symm
    refine Finset.sum_nbij' (fun a => a.2) (fun y => (s, y)) ?_ ?_ ?_ ?_ ?_ <;> simp
    rintro a b rfl; rfl
  have hσy : ∀ y, ∑ s, σ {(s, y)} = μ {y} := by
    intro y
    rw [← hσ2, Measure.map_apply measurable_snd (measurableSet_singleton _), meas_eq_sum]
    symm
    refine Finset.sum_nbij' (fun a => a.1) (fun s => (s, y)) ?_ ?_ ?_ ?_ ?_ <;> simp
  have hσle : ∀ s y, σ {(s, y)} ≤ r {s} := fun s y => by
    rw [← hσs s]
    exact Finset.single_le_sum (f := fun y => σ {(s, y)}) (fun _ _ => by positivity)
      (Finset.mem_univ y)
  have hQle : ∀ a : Cube N × Cube N, Q {a} ≤ r {a.1 ⊓ a.2} := fun a => by
    rw [hrs]; exact Finset.single_le_sum (f := fun a => Q {a}) (fun _ _ => by positivity) (by simp)
  have hrfin : ∀ s, r {s} ≠ ⊤ := fun s => measure_ne_top _ _
  let w : Cube N × Cube N × Cube N → ENNReal := fun z =>
    Q {(z.1, z.2.1)} * σ {(z.1 ⊓ z.2.1, z.2.2)} * (r {z.1 ⊓ z.2.1})⁻¹
  let π : Measure (Cube N × Cube N × Cube N) := ∑ z, w z • Measure.dirac z
  have hπ : ∀ z, π {z} = w z := by
    intro z
    simp only [π, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (measurableSet_singleton _)]
    rw [Finset.sum_eq_single z]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  refine ⟨π, ?_, ?_, ?_⟩
  · refine Measure.ext_of_singleton fun a => ?_
    rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _), meas_eq_sum]
    have : ∑ z ∈ Finset.univ.filter
        (· ∈ (fun z : Cube N × Cube N × Cube N => (z.1, z.2.1)) ⁻¹' {a}), π {z}
        = ∑ y, w (a.1, a.2, y) := by
      refine Finset.sum_nbij' (fun z => z.2.2) (fun y => (a.1, a.2, y)) (by simp) (by simp) ?_
        (by simp) ?_
      · intro z hz
        have hz : (z.1, z.2.1) = a := (Finset.mem_filter.mp hz).2
        subst hz; rfl
      · intro z hz
        have hz : (z.1, z.2.1) = a := (Finset.mem_filter.mp hz).2
        subst hz; exact hπ z
    rw [this]
    simp only [w, ← Finset.sum_mul, ← Finset.mul_sum, hσs]
    by_cases h0 : r {a.1 ⊓ a.2} = 0
    · have := hQle a; rw [h0] at this; rw [le_zero_iff.mp this]; simp
    · rw [mul_assoc, ENNReal.mul_inv_cancel h0 (hrfin _), mul_one]
  · refine Measure.ext_of_singleton fun y => ?_
    rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _), meas_eq_sum]
    have : ∑ z ∈ Finset.univ.filter
        (· ∈ (fun z : Cube N × Cube N × Cube N => z.2.2) ⁻¹' {y}), π {z}
        = ∑ a : Cube N × Cube N, w (a.1, a.2, y) := by
      refine Finset.sum_nbij' (fun z => (z.1, z.2.1)) (fun a => (a.1, a.2, y)) (by simp)
        (by simp) ?_ (by simp) ?_
      · intro z hz
        have hz : z.2.2 = y := (Finset.mem_filter.mp hz).2
        subst hz; rfl
      · intro z hz
        have hz : z.2.2 = y := (Finset.mem_filter.mp hz).2
        subst hz; exact hπ z
    rw [this, ← hσy, ← Finset.sum_fiberwise Finset.univ (fun a : Cube N × Cube N => a.1 ⊓ a.2)]
    refine Finset.sum_congr rfl fun s _ => ?_
    have : ∀ a ∈ Finset.univ.filter (fun a : Cube N × Cube N => a.1 ⊓ a.2 = s),
        w (a.1, a.2, y) = Q {a} * (σ {(s, y)} * (r {s})⁻¹) := by
      intro a ha
      simp only [Finset.mem_filter] at ha
      simp only [w, ha.2, mul_assoc]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← hrs]
    by_cases h0 : r {s} = 0
    · have := hσle s y; rw [h0] at this; rw [le_zero_iff.mp this, h0]; simp
    · rw [mul_comm (σ _), ← mul_assoc, ENNReal.mul_inv_cancel h0 (hrfin _), one_mul]
  · rw [meas_eq_sum]
    refine Finset.sum_eq_zero fun z hz => ?_
    simp only [Finset.mem_filter, Set.mem_compl_iff, Set.mem_ofPred_eq] at hz
    rw [hπ]
    have : σ {(z.1 ⊓ z.2.1, z.2.2)} = 0 :=
      measure_mono_null (by simpa using hz.2) hσ0
    simp [w, this]

theorem main (α : ℝ) (hα0 : 0 < α) (hα : α ≤ (Real.sqrt 5 - 1) / 2)
    (N : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (ν : Measure (Cube N)) (hν0 : IsProbabilityMeasure ν) (hν : IsSpread (α * p) ν) :
    StochDomSubset (retention α ν) (prodLaw N p) ∧
    ∃ π : Measure (Cube N × Cube N × Cube N), IsProbabilityMeasure π ∧
      π.map (fun z : Cube N × Cube N × Cube N => (z.1, z.2.1)) = ν.prod (prodLaw N α) ∧
      π.map (fun z : Cube N × Cube N × Cube N => z.2.2) = prodLaw N p ∧
      π {z : Cube N × Cube N × Cube N | z.1 ⊓ z.2.1 ≤ z.2.2}ᶜ = 0 := by
  have h5 : Real.sqrt 5 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h5sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hα1 : α < 1 := by linarith
  have hq0 : 0 < α * p := mul_pos hα0 hp0
  have hq1 : α * p < 1 := by nlinarith
  have hαα : α ^ 2 + α ≤ 1 := by
    have h0 : 0 ≤ (Real.sqrt 5 - 1) / 2 := by
      have := Real.sqrt_nonneg 5; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)]
    nlinarith
  have hη : α * (α * p) * (1 - p) / (p * (1 - α)) ≤ 1 := by
    rw [div_le_one (by nlinarith)]
    have : α * (α * p) * (1 - p) = p * (α ^ 2 * (1 - p)) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ hp0.le
    nlinarith
  have hdom := (theorem_1_2 α (α * p) hα0 hα1 hq0 hq1 ν hν).1 p hp0 hp1 hη
  refine ⟨hdom, ?_⟩
  obtain ⟨σ, _, hσ0, hσ1, hσ2⟩ := hdom
  have := prodLaw_isProbabilityMeasure N α hα0.le hα1.le
  obtain ⟨π, h1, h2, h3⟩ := glue (ν.prod (prodLaw N α)) σ (prodLaw N p) hσ0 hσ1 hσ2
  refine ⟨π, ⟨?_⟩, h1, h2, h3⟩
  have := prodLaw_isProbabilityMeasure N p hp0.le hp1.le
  have h := congrArg (fun m : Measure (Cube N) => m Set.univ) h2
  rw [Measure.map_apply (measurable_of_finite _) MeasurableSet.univ, Set.preimage_univ] at h
  rw [h, measure_univ]

end TTC13

open TalagrandThinning in
theorem solution :
    (∀ α : ℝ, 0 < α → α ≤ (Real.sqrt 5 - 1) / 2 →
      ∀ N : ℕ, 1 ≤ N → ∀ p : ℝ, 0 < p → p < 1 →
      ∀ ν : Measure (Cube N), IsProbabilityMeasure ν → IsSpread (α * p) ν →
        StochDomSubset (retention α ν) (prodLaw N p) ∧
        ∃ π : Measure (Cube N × Cube N × Cube N), IsProbabilityMeasure π ∧
          π.map (fun z : Cube N × Cube N × Cube N => (z.1, z.2.1)) = ν.prod (prodLaw N α) ∧
          π.map (fun z : Cube N × Cube N × Cube N => z.2.2) = prodLaw N p ∧
          π {z : Cube N × Cube N × Cube N | z.1 ⊓ z.2.1 ≤ z.2.2}ᶜ = 0) ∧
    (∀ N : ℕ, 1 ≤ N → ∀ p : ℝ, 0 < p → p < 1 →
      ∀ ν : Measure (Cube N), IsProbabilityMeasure ν → IsSpread ((1 / 2) * p) ν →
        StochDomSubset (retention (1 / 2) ν) (prodLaw N p) ∧
        ∃ π : Measure (Cube N × Cube N × Cube N), IsProbabilityMeasure π ∧
          π.map (fun z : Cube N × Cube N × Cube N => (z.1, z.2.1)) = ν.prod (prodLaw N (1 / 2)) ∧
          π.map (fun z : Cube N × Cube N × Cube N => z.2.2) = prodLaw N p ∧
          π {z : Cube N × Cube N × Cube N | z.1 ⊓ z.2.1 ≤ z.2.2}ᶜ = 0) := by
  refine ⟨fun α h0 h1 N _ p hp0 hp1 ν hν0 hν => TTC13.main α h0 h1 N p hp0 hp1 ν hν0 hν,
    fun N _ p hp0 hp1 ν hν0 hν => TTC13.main (1 / 2) (by norm_num) ?_ N p hp0 hp1 ν hν0 hν⟩
  have : (2 : ℝ) ≤ Real.sqrt 5 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  linarith
