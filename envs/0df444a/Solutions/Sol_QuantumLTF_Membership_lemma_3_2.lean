-- Prove2me | solution 1 for QuantumLTF.Membership.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-14T17:45:28.715868+00:00
-- url     : https://prove2.me/submissions/aaf268a4-abf9-43c2-a7ee-330942487c0d

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_disagree

namespace QuantumLTF.Membership

open MeasureTheory ProbabilityTheory Real

private lemma inner_map_gaussian {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).map (innerSL ℝ w) = gaussianReal 0 1 := by
  rw [IsGaussian.map_eq_gaussianReal]
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian]
  simp [innerSL_apply_norm, hw]

private lemma inner_upper_tail {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1)
    (a : ℝ) (ha : 0 ≤ a) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real {x | a ≤ inner ℝ w x} ≤
      Real.exp (-a ^ 2 / 2) := by
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) := innerSL ℝ w
  have hmap : (stdGaussian (EuclideanSpace ℝ (Fin n))).map L = gaussianReal 0 1 := by
    simpa [L] using inner_map_gaussian w hw
  have hint : Integrable (fun x => Real.exp (a * L x))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    rw [← mgf_pos_iff]
    rw [mgf_gaussianReal hmap]
    positivity
  have hchernoff := measure_ge_le_exp_mul_mgf (μ := stdGaussian (EuclideanSpace ℝ (Fin n)))
    (X := L) a ha hint
  rw [mgf_gaussianReal hmap] at hchernoff
  rw [← Real.exp_add] at hchernoff
  convert hchernoff using 1 <;> simp [L] <;> ring

private lemma inner_lower_tail {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1)
    (a : ℝ) (ha : a ≤ 0) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real {x | inner ℝ w x ≤ a} ≤
      Real.exp (-a ^ 2 / 2) := by
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) := innerSL ℝ w
  have hmap : (stdGaussian (EuclideanSpace ℝ (Fin n))).map L = gaussianReal 0 1 := by
    simpa [L] using inner_map_gaussian w hw
  have hint : Integrable (fun x => Real.exp (a * L x))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    rw [← mgf_pos_iff]
    rw [mgf_gaussianReal hmap]
    positivity
  have hchernoff := measure_le_le_exp_mul_mgf (μ := stdGaussian (EuclideanSpace ℝ (Fin n)))
    (X := L) a ha hint
  rw [mgf_gaussianReal hmap] at hchernoff
  rw [← Real.exp_add] at hchernoff
  convert hchernoff using 1 <;> simp [L] <;> ring

end QuantumLTF.Membership

open QuantumLTF.Membership ProbabilityTheory MeasureTheory

theorem solution {n : ℕ} (hn : 2 ≤ n) (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) (θ ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) (hθ : Real.sqrt (2 * Real.log (1 / ε)) ≤ |θ|) :
    disagree (ltf w θ) (fun _ => ltf w θ 0) ≤ ε := by
  have hdiv : 1 < 1 / ε := (one_lt_div₀ hε₀).2 hε₁
  have hlog : 0 < Real.log (1 / ε) := Real.log_pos hdiv
  have hsqrt : 0 < Real.sqrt (2 * Real.log (1 / ε)) := Real.sqrt_pos.2 (mul_pos two_pos hlog)
  have hθabs : 0 < |θ| := lt_of_lt_of_le hsqrt hθ
  have hsq : 2 * Real.log (1 / ε) ≤ θ ^ 2 := by
    have := (sq_le_sq₀ (Real.sqrt_nonneg _) (abs_nonneg θ)).2 hθ
    rw [Real.sq_sqrt (mul_nonneg (by positivity) hlog.le), sq_abs] at this
    exact this
  have hlog_inv : Real.log (1 / ε) = - Real.log ε := by
    rw [one_div, Real.log_inv]
  have hexp : Real.exp (-θ ^ 2 / 2) ≤ ε := by
    rw [← Real.exp_log hε₀, Real.exp_le_exp]
    rw [hlog_inv] at hsq
    linarith
  rw [disagree]
  by_cases hθnonneg : 0 ≤ θ
  · have hθpos : 0 < θ := lt_of_le_of_ne hθnonneg (Ne.symm (abs_pos.mp hθabs))
    have hset :
        {x | ltf w θ x ≠ ltf w θ 0} = {x | θ ≤ inner ℝ w x} := by
      ext x
      simp [ltf, sgn, sub_nonneg, not_le.mpr hθpos]
    rw [hset]
    exact (inner_upper_tail w hw θ hθnonneg).trans hexp
  · have hθneg : θ < 0 := lt_of_not_ge hθnonneg
    have hset :
        {x | ltf w θ x ≠ ltf w θ 0} = {x | inner ℝ w x < θ} := by
      ext x
      simp [ltf, sgn, sub_nonneg, hθneg.le]
    rw [hset]
    calc
      (stdGaussian (EuclideanSpace ℝ (Fin n))).real {x | inner ℝ w x < θ}
          ≤ (stdGaussian (EuclideanSpace ℝ (Fin n))).real {x | inner ℝ w x ≤ θ} := by
            apply ENNReal.toReal_mono
            · exact measure_ne_top _ _
            · exact measure_mono (by
                intro x hx
                change inner ℝ w x ≤ θ
                exact le_of_lt hx)
      _ ≤ Real.exp (-θ ^ 2 / 2) := inner_lower_tail w hw θ hθneg.le
      _ ≤ ε := hexp
