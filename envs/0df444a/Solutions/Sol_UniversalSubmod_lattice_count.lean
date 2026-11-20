-- Prove2me | solution 1 for UniversalSubmod.lattice_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:47:07.260589+00:00
-- url     : https://prove2.me/submissions/ce9f4bb4-80af-42eb-8a72-7f3d6f4e6b6a

import Mathlib

section
set_option autoImplicit false

namespace UniversalSubmod.Dev.Lattice

open MeasureTheory

/-- the unit cube centered at a lattice point, in Euclidean space -/
def cube (k : ℕ) (y : Fin k → ℤ) : Set (EuclideanSpace ℝ (Fin k)) :=
  (WithLp.ofLp) ⁻¹' (Set.pi Set.univ fun i => Set.Ico ((y i : ℝ) - 1/2) ((y i : ℝ) + 1/2))

lemma cube_meas (k : ℕ) (y : Fin k → ℤ) : MeasurableSet (cube k y) := by
  unfold cube
  exact (MeasurableSet.univ_pi fun i => measurableSet_Ico).preimage
    (MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm.measurable

lemma cube_volume (k : ℕ) (y : Fin k → ℤ) : volume (cube k y) = 1 := by
  unfold cube
  have h2 := (PiLp.volume_preserving_ofLp (Fin k)).measure_preimage
    (s := Set.pi Set.univ fun i => Set.Ico ((y i : ℝ) - 1/2) ((y i : ℝ) + 1/2))
    (MeasurableSet.univ_pi fun i => measurableSet_Ico).nullMeasurableSet
  rw [h2, Real.volume_pi_Ico]
  simp only [add_sub_sub_cancel, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

lemma cube_disj (k : ℕ) : Pairwise (fun y y' : Fin k → ℤ => Disjoint (cube k y) (cube k y')) := by
  intro y y' hne
  rw [Set.disjoint_left]
  intro x hx hx'
  apply hne
  funext i
  have h1 := hx i (Set.mem_univ i)
  have h2 := hx' i (Set.mem_univ i)
  simp only [Set.mem_Ico] at h1 h2
  have a : ((y i : ℤ) : ℝ) < y' i + 1 := by linarith [h1.1, h2.2]
  have b : ((y' i : ℤ) : ℝ) < y i + 1 := by linarith [h1.2, h2.1]
  have a' : y i < y' i + 1 := by exact_mod_cast a
  have b' : y' i < y i + 1 := by exact_mod_cast b
  omega

lemma cube_sub (k : ℕ) (ρ : ℝ) (hρ : Real.sqrt k / 2 ≤ ρ) (y : Fin k → ℤ)
    (hy : ∑ i, ((y i : ℤ) : ℝ) ^ 2 ≤ ρ ^ 2) :
    cube k y ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) (2 * ρ) := by
  intro x hx
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
  have hxy : ∀ i, (x i - (y i : ℝ)) ^ 2 ≤ 1 / 4 := by
    intro i
    have h := hx i (Set.mem_univ i)
    simp only [Set.mem_Ico] at h
    nlinarith [h.1, h.2]
  -- ‖x‖ ≤ ‖y‖ + ‖x - y‖ via Minkowski, done through the norm on EuclideanSpace
  let yE : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 (fun i => ((y i : ℤ) : ℝ))
  have hyE : ‖yE‖ ≤ ρ := by
    rw [EuclideanSpace.norm_eq]
    apply Real.sqrt_le_iff.mpr
    refine ⟨hρ0, ?_⟩
    simpa [yE] using hy
  have hxy' : ‖x - yE‖ ≤ Real.sqrt k / 2 := by
    rw [EuclideanSpace.norm_eq]
    have : ∑ i, ‖(x - yE) i‖ ^ 2 ≤ k * (1 / 4) := by
      calc ∑ i, ‖(x - yE) i‖ ^ 2 ≤ ∑ _i : Fin k, (1 / 4 : ℝ) := by
            apply Finset.sum_le_sum
            intro i _
            simpa [yE] using hxy i
        _ = k * (1 / 4) := by simp
    calc Real.sqrt (∑ i, ‖(x - yE) i‖ ^ 2) ≤ Real.sqrt (k * (1 / 4)) := Real.sqrt_le_sqrt this
      _ = Real.sqrt k / 2 := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
          ring
  have : ‖x‖ ≤ ‖yE‖ + ‖x - yE‖ := by
    have := norm_add_le yE (x - yE)
    simpa using this
  rw [← EuclideanSpace.norm_eq]
  linarith

lemma finite_B (k : ℕ) (ρ : ℝ) :
    {y : Fin k → ℤ | ∑ i, ((y i : ℤ) : ℝ) ^ 2 ≤ ρ ^ 2}.Finite := by
  apply (Set.finite_Icc (fun _ : Fin k => -⌈|ρ|⌉) (fun _ => ⌈|ρ|⌉)).subset
  intro y hy
  have hbd : ∀ i, |(y i : ℝ)| ≤ |ρ| := by
    intro i
    have h1 : ((y i : ℤ) : ℝ) ^ 2 ≤ ρ ^ 2 :=
      le_trans (Finset.single_le_sum (f := fun j => ((y j : ℤ) : ℝ) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)) hy
    exact sq_le_sq.mp h1
  have hc : ∀ i, |y i| ≤ ⌈|ρ|⌉ := by
    intro i
    have : ((|y i| : ℤ) : ℝ) ≤ ⌈|ρ|⌉ := by
      push_cast
      exact (hbd i).trans (Int.le_ceil _)
    exact_mod_cast this
  constructor <;> intro i
  · exact neg_le_of_abs_le (hc i)
  · exact le_of_abs_le (hc i)

end UniversalSubmod.Dev.Lattice

namespace UniversalSubmod

open MeasureTheory

theorem chk_lattice_count (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ) (hρ : Real.sqrt k / 2 ≤ ρ) :
    let B : Set (Fin k → ℤ) := {y | ∑ i, ((y i : ℤ) : ℝ) ^ 2 ≤ ρ ^ 2}
    B.Finite ∧
    (B.ncard : ℝ) ≤
      (2 * ρ) ^ k * (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)).toReal ∧
    (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)).toReal ≤
      ∫ y : EuclideanSpace ℝ (Fin k), Real.exp ((k : ℝ) * (1 - ‖y‖ ^ 2) / 2) ∧
    (2 * ρ) ^ k * ∫ y : EuclideanSpace ℝ (Fin k), Real.exp ((k : ℝ) * (1 - ‖y‖ ^ 2) / 2) =
      (2 * ρ * Real.sqrt (2 * Real.pi * Real.exp 1 / k)) ^ k := by
  intro B
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ
  have hfin : B.Finite := Dev.Lattice.finite_B k ρ
  have hfrk : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := by simp
  have hball : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) (2 * ρ)) =
      ENNReal.ofReal ((2 * ρ) ^ k) *
        volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) := by
    rw [Measure.addHaar_closedBall' volume _ (by positivity), hfrk]
  have hvfin : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) < ⊤ :=
    measure_closedBall_lt_top
  -- link 2
  have hcount : (B.ncard : ℝ) ≤
      (2 * ρ) ^ k * (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)).toReal := by
    have hU : volume (⋃ y ∈ hfin.toFinset, Dev.Lattice.cube k y) =
        (hfin.toFinset.card : ENNReal) := by
      rw [measure_biUnion_finset (fun y _ y' _ h => Dev.Lattice.cube_disj k h)
        (fun y _ => Dev.Lattice.cube_meas k y)]
      simp [Dev.Lattice.cube_volume]
    have hsub : (⋃ y ∈ hfin.toFinset, Dev.Lattice.cube k y) ⊆
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) (2 * ρ) := by
      apply Set.iUnion₂_subset
      intro y hy
      exact Dev.Lattice.cube_sub k ρ hρ y (hfin.mem_toFinset.mp hy)
    have h1 := measure_mono (μ := volume) hsub
    rw [hU, hball] at h1
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvfin.ne) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
    rw [Set.ncard_eq_toFinset_card B hfin]
    simpa using h2
  -- Gaussian integral
  have hb : (0 : ℝ) < k / 2 := by positivity
  have hG : ∫ y : EuclideanSpace ℝ (Fin k), Real.exp (-((k : ℝ) / 2) * ‖y‖ ^ 2) =
      (Real.pi / ((k : ℝ) / 2)) ^ ((k : ℝ) / 2) := by
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, hfrk]
  have hGpos : (0 : ℝ) < (Real.pi / ((k : ℝ) / 2)) ^ ((k : ℝ) / 2) := by positivity
  have hGint : Integrable (fun y : EuclideanSpace ℝ (Fin k) =>
      Real.exp (-((k : ℝ) / 2) * ‖y‖ ^ 2)) := by
    apply Integrable.of_integral_ne_zero
    rw [hG]; exact hGpos.ne'
  have hrew : (fun y : EuclideanSpace ℝ (Fin k) => Real.exp ((k : ℝ) * (1 - ‖y‖ ^ 2) / 2)) =
      fun y => Real.exp ((k : ℝ) / 2) * Real.exp (-((k : ℝ) / 2) * ‖y‖ ^ 2) := by
    funext y; rw [← Real.exp_add]; congr 1; ring
  have hint : Integrable (fun y : EuclideanSpace ℝ (Fin k) =>
      Real.exp ((k : ℝ) * (1 - ‖y‖ ^ 2) / 2)) := by
    rw [hrew]; exact hGint.const_mul _
  have hI : ∫ y : EuclideanSpace ℝ (Fin k), Real.exp ((k : ℝ) * (1 - ‖y‖ ^ 2) / 2) =
      Real.exp ((k : ℝ) / 2) * (Real.pi / ((k : ℝ) / 2)) ^ ((k : ℝ) / 2) := by
    rw [hrew, integral_const_mul, hG]
  refine ⟨hfin, hcount, ?_, ?_⟩
  · -- link 3
    have hvol : (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)).toReal =
        ∫ y, (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1).indicator
          (fun _ => (1 : ℝ)) y := by
      rw [integral_indicator_const _ measurableSet_closedBall]
      simp [Measure.real]
    rw [hvol]
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun y => Set.indicator_nonneg (fun _ _ => zero_le_one) y)
    · exact hint
    · refine Filter.Eventually.of_forall (fun y => ?_)
      by_cases hy : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1
      · rw [Set.indicator_of_mem hy]
        rw [mem_closedBall_zero_iff] at hy
        apply Real.one_le_exp_iff.mpr
        have : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
        have : 0 ≤ (k : ℝ) * (1 - ‖y‖ ^ 2) := mul_nonneg hkpos.le (by linarith)
        linarith
      · rw [Set.indicator_of_notMem hy]
        exact (Real.exp_pos _).le
  · -- link 4
    rw [hI]
    have h2 : Real.sqrt (2 * Real.pi * Real.exp 1 / k) ^ k =
        Real.exp ((k : ℝ) / 2) * (Real.pi / ((k : ℝ) / 2)) ^ ((k : ℝ) / 2) := by
      have e1 : 2 * Real.pi * Real.exp 1 / k = Real.exp 1 * (Real.pi / ((k : ℝ) / 2)) := by
        field_simp
      have e2 : (1 / 2 : ℝ) * k = k / 2 := by ring
      rw [e1, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        Real.mul_rpow (by positivity) (by positivity), e2, Real.exp_one_rpow]
    rw [mul_pow (2 * ρ), ← h2]
end UniversalSubmod
end

theorem solution : type_of% @UniversalSubmod.chk_lattice_count := @UniversalSubmod.chk_lattice_count
