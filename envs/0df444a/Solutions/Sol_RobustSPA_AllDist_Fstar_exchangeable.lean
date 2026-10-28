-- Prove2me | solution 1 for RobustSPA.AllDist.Fstar_exchangeable
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T08:28:32.680434+00:00
-- url     : https://prove2.me/submissions/66521ab3-4ab5-4892-865b-84a2850c5eec

import Mathlib
import Definitions.Def_RobustSPA_AllDist_Setting
open MeasureTheory

namespace RSPA3
open RobustSPA.AllDist

lemma meas_single {n : ℕ} (k : Fin n) :
    Measurable (fun t : ℝ => (Pi.single k t : Fin n → ℝ)) := by
  refine measurable_pi_lambda _ (fun j => ?_)
  by_cases h : j = k
  · subst h; simp only [Pi.single_eq_same]; exact measurable_id'
  · simp [h]

lemma single_mem_cube_iff {n : ℕ} (k : Fin n) (t : ℝ) :
    (Pi.single k t : Fin n → ℝ) ∈ cube n ↔ t ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · intro h
    have := h k (Set.mem_univ _)
    simpa using this
  · intro ht j _
    by_cases hj : j = k
    · subst hj; simpa using ht
    · simp [Pi.single_apply, hj]

lemma measurableSet_cube (n : ℕ) : MeasurableSet (cube n) := by
  unfold cube
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

lemma Fstar_apply {n : ℕ} (G : Measure ℝ) (s : Set (Fin n → ℝ)) (hs : MeasurableSet s) :
    Fstar n G s = (n : ENNReal)⁻¹ * ∑ k : Fin n, G ((fun t : ℝ => (Pi.single k t : Fin n → ℝ)) ⁻¹' s) := by
  unfold Fstar
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Measure.map_apply (meas_single k) hs]

theorem Fstar_mem_Fexc (n : ℕ) (hn : 0 < n) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : G (Set.Icc 0 1)ᶜ = 0) : Fstar n G ∈ Fexc n := by
  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · rw [Fstar_apply G _ MeasurableSet.univ]
    simp only [Set.preimage_univ, measure_univ, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    have : (n : ENNReal) ≠ 0 := by exact_mod_cast hn.ne'
    exact ENNReal.inv_mul_cancel this (ENNReal.natCast_ne_top n)
  · rw [Fstar_apply G _ (measurableSet_cube n).compl]
    have : ∀ k : Fin n, G ((fun t : ℝ => (Pi.single k t : Fin n → ℝ)) ⁻¹' (cube n)ᶜ) = 0 := by
      intro k
      have hpre : ((fun t : ℝ => (Pi.single k t : Fin n → ℝ)) ⁻¹' (cube n)ᶜ) = (Set.Icc 0 1)ᶜ := by
        ext t; simp [single_mem_cube_iff]
      rw [hpre, hG]
    rw [Finset.sum_eq_zero (fun k _ => this k), mul_zero]
  · intro σ
    ext s hs
    have hmσ : Measurable (fun v : Fin n → ℝ => v ∘ σ) := by fun_prop
    rw [Measure.map_apply hmσ hs, Fstar_apply G _ (hmσ hs), Fstar_apply G _ hs]
    congr 1
    have key : ∀ k : Fin n, ((fun t : ℝ => (Pi.single k t : Fin n → ℝ)) ⁻¹' ((fun v : Fin n → ℝ => v ∘ σ) ⁻¹' s))
        = (fun t : ℝ => (Pi.single (σ.symm k) t : Fin n → ℝ)) ⁻¹' s := by
      intro k
      ext t
      simp only [Set.mem_preimage]
      have : ((Pi.single k t : Fin n → ℝ) ∘ σ) = Pi.single (σ.symm k) t := by
        funext j
        simp only [Function.comp, Pi.single_apply]
        congr 1
        exact propext ⟨fun h => by rw [← h]; simp, fun h => by rw [h]; simp⟩
      rw [this]
    simp_rw [key]
    exact Equiv.sum_comp σ.symm (fun k => G ((fun t : ℝ => (Pi.single k t : Fin n → ℝ)) ⁻¹' s))

end RSPA3

theorem solution (n : ℕ) (hn : 0 < n) (G : ProbabilityMeasure ℝ)
    (hG : (G : Measure ℝ) (Set.Icc 0 1)ᶜ = 0) :
    RobustSPA.AllDist.Fstar n (G : Measure ℝ) ∈ RobustSPA.AllDist.Fexc n :=
  RSPA3.Fstar_mem_Fexc n hn G hG
