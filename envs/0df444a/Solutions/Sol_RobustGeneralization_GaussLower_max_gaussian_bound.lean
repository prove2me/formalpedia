-- Prove2me | solution 1 for RobustGeneralization.GaussLower.max_gaussian_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:09:03.729686+00:00
-- url     : https://prove2.me/submissions/0a86d8cc-6bb6-44e2-9250-f724ad4562af

import Mathlib
import Definitions.Def_RobustGeneralization_GaussLower_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussLower

lemma aux_mgb_upper (t : ℝ) (ht : 0 ≤ t) :
    (gaussianReal 0 1).real {x | t ≤ x} ≤ Real.exp (-(t ^ 2) / 2) := by
  have h := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := fun x => x) t ht
    (integrable_exp_mul_gaussianReal t)
  rw [mgf_fun_id_gaussianReal] at h
  refine h.trans (le_of_eq ?_)
  rw [← Real.exp_add]; congr 1; push_cast; ring

lemma aux_mgb_lower (t : ℝ) (ht : 0 ≤ t) :
    (gaussianReal 0 1).real {x | x ≤ -t} ≤ Real.exp (-(t ^ 2) / 2) := by
  have h := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := fun x => x) (t := -t) (-t)
    (by linarith) (integrable_exp_mul_gaussianReal (-t))
  rw [mgf_fun_id_gaussianReal] at h
  refine h.trans (le_of_eq ?_)
  rw [← Real.exp_add]; congr 1; push_cast; ring

lemma aux_mgb_Icc (t : ℝ) (ht : 0 ≤ t) :
    1 - 2 * Real.exp (-(t ^ 2) / 2) ≤ (gaussianReal 0 1).real (Set.Icc (-t) t) := by
  have h1 := aux_mgb_upper t ht
  have h2 := aux_mgb_lower t ht
  have hc : (Set.Icc (-t) t)ᶜ ⊆ {x | x ≤ -t} ∪ {x | t ≤ x} := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · left; exact le_of_lt hx
    · right; exact le_of_lt hx
  have h3 : (gaussianReal 0 1).real (Set.Icc (-t) t)ᶜ ≤
      (gaussianReal 0 1).real {x | x ≤ -t} + (gaussianReal 0 1).real {x | t ≤ x} :=
    (measureReal_mono hc).trans (measureReal_union_le _ _)
  rw [measureReal_compl measurableSet_Icc, probReal_univ] at h3
  linarith

lemma aux_mgb_real (d : ℕ) (q : ℝ) (hq0 : 0 ≤ q)
    (hq : 1 - 2 * Real.exp (-((2 * Real.sqrt (2 * Real.log d)) ^ 2) / 2) ≤ q) :
    1 - 1 / (d : ℝ) ≤ q ^ d := by
  rcases Nat.lt_or_ge d 2 with hd | hd
  · interval_cases d
    · simp
    · simpa using hq0
  · have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hdpos : (0 : ℝ) < d := by linarith
    have hlog : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
    set e := Real.exp (-((2 * Real.sqrt (2 * Real.log d)) ^ 2) / 2) with he
    have hepos : 0 < e := Real.exp_pos _
    have hed : e * (d : ℝ) ^ 4 = 1 := by
      have hsq : (2 * Real.sqrt (2 * Real.log d)) ^ 2 = 8 * Real.log d := by
        rw [mul_pow, Real.sq_sqrt (by linarith)]; ring
      have hd4 : (d : ℝ) ^ 4 = Real.exp (4 * Real.log d) := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hdpos]
      rw [he, hsq, hd4, ← Real.exp_add]
      rw [← Real.exp_zero]; congr 1; ring
    have hb := one_add_mul_le_pow (a := q - 1) (by linarith) d
    rw [add_sub_cancel] at hb
    -- 1 - 1/d ≤ 1 + d (q - 1)
    have key : (d : ℝ) * (1 - q) ≤ 1 / d := by
      rw [le_div_iff₀ hdpos]
      have h1 : (d : ℝ) * (1 - q) * d ≤ 2 * e * d ^ 2 := by
        have : 1 - q ≤ 2 * e := by linarith
        nlinarith
      have h2 : 2 * e * (d : ℝ) ^ 2 ≤ 1 := by
        rw [← hed]
        have hd2 : (2 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
        have : 2 * e * (d : ℝ) ^ 2 ≤ e * (d : ℝ) ^ 2 * (d : ℝ) ^ 2 := by
          have := mul_le_mul_of_nonneg_left hd2 (le_of_lt (mul_pos hepos (by positivity : (0:ℝ) < (d:ℝ)^2)))
          nlinarith
        nlinarith
      linarith
    linarith

theorem aux_mgb_main (d : ℕ) :
    ENNReal.ofReal (1 - 1 / (d : ℝ)) ≤
      stdGaussian (E d) {v | ∀ i, |v i| ≤ 2 * Real.sqrt (2 * Real.log d)} := by
  set t := 2 * Real.sqrt (2 * Real.log d) with ht_def
  have ht0 : 0 ≤ t := by positivity
  have hmeas : MeasurableSet {v : E d | ∀ i, |v i| ≤ t} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le (by fun_prop) measurable_const
  rw [← map_pi_eq_stdGaussian, Measure.map_apply (by fun_prop) hmeas]
  have hpre : (WithLp.toLp 2 : (Fin d → ℝ) → E d) ⁻¹' {v | ∀ i, |v i| ≤ t} =
      Set.univ.pi (fun _ => Set.Icc (-t) t) := by
    ext x; simp [abs_le, Pi.le_def, forall_and]
  rw [hpre, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ofReal_measureReal, ← ENNReal.ofReal_pow measureReal_nonneg]
  apply ENNReal.ofReal_le_ofReal
  exact aux_mgb_real d _ measureReal_nonneg (aux_mgb_Icc t ht0)

end RobustGeneralization.GaussLower

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open RobustGeneralization.GaussLower

theorem solution (d : ℕ) :
    ENNReal.ofReal (1 - 1 / (d : ℝ)) ≤
      stdGaussian (E d) {v | ∀ i, |v i| ≤ 2 * Real.sqrt (2 * Real.log d)} :=
  aux_mgb_main d
