-- Prove2me | solution 1 for WassersteinDRO.Gelbrich.gelbrich_hull_containment_false
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:04:49.97185+00:00
-- url     : https://prove2.me/submissions/540e1ee5-35a6-4c1c-a924-58cc62e0784e

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_ambiguitySet
import Definitions.Def_WassersteinDRO_Gelbrich_gelbrichHull
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

open WassersteinDRO.Gelbrich
set_option maxHeartbeats 0

private noncomputable def weight (i : ℕ × Fin 2) : ℝ≥0∞ :=
  (3 / 8 : ℝ≥0∞) * (1 / 4 : ℝ≥0∞) ^ i.1

private noncomputable def point (i : ℕ × Fin 2) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun j => if j = 0 then (if i.2 = 0 then 1 else -1)
    else (if i.2 = 0 then (2 : ℝ) ^ i.1 else -(2 : ℝ) ^ i.1))

private noncomputable def law : Measure (EuclideanSpace ℝ (Fin 2)) :=
  Measure.sum (fun i : ℕ × Fin 2 => weight i • Measure.dirac (point i))

private theorem weight_finite (i : ℕ × Fin 2) : weight i ≠ ∞ := by
  dsimp [weight]
  finiteness

private theorem weight_real (i : ℕ × Fin 2) :
    (weight i).toReal = (3 / 8 : ℝ) * (1 / 4 : ℝ) ^ i.1 := by
  simp [weight, ENNReal.toReal_mul, ENNReal.toReal_pow]

private theorem law_mass : law Set.univ = 1 := by
  rw [law, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [ENNReal.tsum_prod']
  simp only [weight, tsum_fintype, Fin.sum_univ_two]
  simp_rw [← add_mul]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have hsub : (1 : ℝ≥0∞) - 1 / 4 = 3 / 4 := by
    apply ENNReal.sub_eq_of_eq_add (by finiteness)
    rw [ENNReal.div_add_div_same]
    norm_num
    rw [ENNReal.div_self (by norm_num) (by finiteness)]
  rw [hsub]
  rw [ENNReal.div_add_div_same]
  norm_num
  rw [ENNReal.inv_div (by left; finiteness) (by left; norm_num),
    ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  rw [mul_mul_mul_comm, ← ENNReal.mul_inv]
  norm_num
  rw [ENNReal.inv_mul_cancel (by norm_num) (by finiteness)]
  all_goals norm_num

private theorem law_mean : meanVector law = 0 := by
  rw [meanVector, law, integral_sum_dirac weight_finite]
  by_cases h : Summable (fun i : ℕ × Fin 2 => (weight i).toReal • point i)
  · rw [h.tsum_prod]
    have hp : ∀ n : ℕ, ∑' b : Fin 2, (weight (n, b)).toReal • point (n, b) = 0 := by
      intro n
      rw [tsum_fintype, Fin.sum_univ_two]
      apply (WithLp.ext_iff 2).mpr
      funext j
      fin_cases j <;> simp +decide [point, weight_real] <;> ring
    simp_rw [hp]
    simp
  · exact tsum_eq_zero_of_not_summable h

private theorem geo_pair (a r : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r) (hr1 : r < 1) :
    (∑' i : ℕ × Fin 2, a * r ^ i.1) = 2 * a * (1 - r)⁻¹ := by
  have hs : Summable (fun i : ℕ × Fin 2 => a * r ^ i.1) := by
    apply (summable_prod_of_nonneg (fun i => mul_nonneg ha (pow_nonneg hr _))).mpr
    refine ⟨fun n => (hasSum_fintype _).summable, ?_⟩
    simpa [tsum_fintype, Fin.sum_univ_two, ← two_mul, mul_assoc] using
      (summable_geometric_of_lt_one hr hr1).mul_left (2 * a)
  rw [hs.tsum_prod]
  simp only [tsum_fintype, Fin.sum_univ_two, ← two_mul, mul_assoc]
  rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hr hr1]

private theorem law_cov : covarianceMatrix law = !![1, 3 / 2; 3 / 2, 0] := by
  ext i j
  simp only [covarianceMatrix, Matrix.of_apply, law_mean, WithLp.ofLp_zero, Pi.zero_apply, sub_zero]
  rw [law, integral_sum_dirac weight_finite]
  simp only [smul_eq_mul]
  fin_cases i <;> fin_cases j
  all_goals simp only [Fin.zero_eta, Fin.mk_one]
  · have h : (fun i : ℕ × Fin 2 => (weight i).toReal * (point i 0 * point i 0)) =
        (fun i : ℕ × Fin 2 => (3 / 8 : ℝ) * (1 / 4 : ℝ) ^ i.1) := by
      funext i
      rcases i with ⟨n, b⟩
      fin_cases b <;> simp +decide [point, weight_real] <;> ring
    rw [h, geo_pair (3 / 8) (1 / 4) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  · have h : (fun i : ℕ × Fin 2 => (weight i).toReal * (point i 0 * point i 1)) =
        (fun i : ℕ × Fin 2 => (3 / 8 : ℝ) * (1 / 2 : ℝ) ^ i.1) := by
      funext i
      rcases i with ⟨n, b⟩
      fin_cases b <;> simp +decide [point, weight_real]
      all_goals rw [← inv_pow, ← inv_pow, mul_assoc, ← mul_pow]; norm_num
    rw [h, geo_pair (3 / 8) (1 / 2) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  · have h : (fun i : ℕ × Fin 2 => (weight i).toReal * (point i 1 * point i 0)) =
        (fun i : ℕ × Fin 2 => (3 / 8 : ℝ) * (1 / 2 : ℝ) ^ i.1) := by
      funext i
      rcases i with ⟨n, b⟩
      fin_cases b <;> simp +decide [point, weight_real]
      all_goals rw [← inv_pow, ← inv_pow, mul_assoc, ← mul_pow]; norm_num
    rw [h, geo_pair (3 / 8) (1 / 2) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  · have h : (fun i : ℕ × Fin 2 => (weight i).toReal * (point i 1 * point i 1)) =
        (fun _ : ℕ × Fin 2 => (3 / 8 : ℝ)) := by
      funext i
      rcases i with ⟨n, b⟩
      fin_cases b <;> simp +decide [point, weight_real]
      all_goals
        have hp : (4 : ℝ)^n = (2 : ℝ)^n * (2 : ℝ)^n := by rw [← mul_pow]; norm_num
        rw [hp]
        field_simp
        <;> ring
    rw [h, tsum_eq_zero_of_not_summable]
    · rfl
    · intro hs
      letI := Finite.of_summable_const (by norm_num : (0 : ℝ) < 3 / 8) hs
      exact not_finite (ℕ × Fin 2)

private theorem law_not_psd : ¬ (covarianceMatrix law).PosSemidef := by
  rw [law_cov]
  intro h
  have hi := h.dotProduct_mulVec_nonneg ![1, -1]
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hi

private theorem diagonal_distance (Q : Measure (EuclideanSpace ℝ (Fin 2))) :
    wassersteinDistance 2 Q Q = 0 := by
  let π := Q.map (fun x => (x, x))
  have hm : π.map Prod.fst = Q ∧ π.map Prod.snd = Q := by
    dsimp [π]
    have hd : Measurable (fun x : EuclideanSpace ℝ (Fin 2) => (x, x)) := by fun_prop
    rw [Measure.map_map measurable_fst hd, Measure.map_map measurable_snd hd]
    exact ⟨Measure.map_id, Measure.map_id⟩
  have hc : (∫⁻ x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      ENNReal.ofReal (‖x.1 - x.2‖ ^ (2 : ℝ)) ∂π) = 0 := by
    rw [lintegral_map (by fun_prop) (by fun_prop)]
    simp
  have hi : (⨅ (π : Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
      (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = Q),
      ∫⁻ x, ENNReal.ofReal (‖x.1 - x.2‖ ^ (2 : ℝ)) ∂π) = 0 := by
    apply le_antisymm _ bot_le
    exact iInf_le_of_le π (iInf_le_of_le hm hc.le)
  unfold wassersteinDistance
  rw [hi]
  norm_num

theorem solution :
    ¬∀ {m : ℕ} (ε p : ℝ), 2 ≤ p → (Ξ : Set (EuclideanSpace ℝ (Fin m))) →
      (PN : Measure (EuclideanSpace ℝ (Fin m))) →
      (μhat : EuclideanSpace ℝ (Fin m)) → (SigmaHat : Matrix (Fin m) (Fin m) ℝ) →
      meanVector PN = μhat → covarianceMatrix PN = SigmaHat →
      ambiguitySet ε p Ξ PN ⊆ gelbrichHull ε Ξ μhat SigmaHat := by
  intro h
  have hin : law ∈ ambiguitySet 1 2 Set.univ law := by
    refine ⟨law_mass, by simp, ?_⟩
    rw [diagonal_distance]
    exact bot_le
  have hout := h 1 2 (by norm_num) Set.univ law (meanVector law) (covarianceMatrix law)
    rfl rfl hin
  exact law_not_psd hout.2.2.1


#print axioms solution
