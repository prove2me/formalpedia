-- Prove2me | solution 1 for RobustSAA.Discrete.tv_weak
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:36:49.52021+00:00
-- url     : https://prove2.me/submissions/a72495f1-63ca-45e1-9b55-de9e97ab698b

import Definitions.Def_RobustSAA_Discrete_Setting
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.Order
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open MeasureTheory Filter Finset RobustSAA.Discrete
open scoped Topology BigOperators BoundedContinuousFunction

private lemma integral_as_sum {n : ℕ} (P : ProbabilityMeasure (Fin n))
    (f : Fin n →ᵇ ℝ) : ∫ x, f x ∂(P : Measure (Fin n)) = ∑ j, pvec P j * f j := by
  simpa only [pvec, smul_eq_mul] using integral_fintype (f.integrable (μ := (P : Measure (Fin n))))

private lemma weak_coordinates {n : ℕ} (G : ℕ → ProbabilityMeasure (Fin n))
    (P : ProbabilityMeasure (Fin n)) :
    Tendsto G atTop (𝓝 P) ↔ ∀ j, Tendsto (fun N => pvec (G N) j) atTop (𝓝 (pvec P j)) := by
  classical
  constructor
  · intro h j
    let f : Fin n →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
      ⟨fun x => if x = j then 1 else 0, continuous_of_discreteTopology⟩
    have hf (Q : ProbabilityMeasure (Fin n)) : ∫ x, f x ∂(Q : Measure (Fin n)) = pvec Q j := by
      rw [integral_as_sum]
      simp [f]
    have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h f
    simpa only [hf] using ht
  · intro h
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    simp_rw [integral_as_sum]
    exact tendsto_finset_sum univ (fun j _ => (h j).mul_const (f j))

theorem solution (n : ℕ) (G : ℕ → ProbabilityMeasure (Fin n))
    (F : ProbabilityMeasure (Fin n)) :
    Tendsto G atTop (𝓝 F) ↔
      Tendsto (fun N => dTV (pvec (G N)) (pvec F)) atTop (𝓝 0) := by
  classical
  rw [weak_coordinates]
  constructor
  · intro h
    have hs := tendsto_finset_sum univ (fun j _ => ((h j).sub_const (pvec F j)).abs)
    have ht := (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul hs
    simpa only [sub_self, abs_zero, sum_const_zero, mul_zero, dTV] using ht
  · intro h j
    have hu : Tendsto (fun N => 2 * dTV (pvec (G N)) (pvec F)) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds (x := (2 : ℝ))).mul h
    have habs : Tendsto (fun N => |pvec (G N) j - pvec F j|) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ => abs_nonneg _) (fun N => ?_) hu
      have hs : |pvec (G N) j - pvec F j| ≤ ∑ k, |pvec (G N) k - pvec F k| :=
        single_le_sum (f := fun k : Fin n => |pvec (G N) k - pvec F k|) (fun k _ => abs_nonneg _) (mem_univ j)
      dsimp [dTV]
      linarith
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq] using habs

#print axioms solution



