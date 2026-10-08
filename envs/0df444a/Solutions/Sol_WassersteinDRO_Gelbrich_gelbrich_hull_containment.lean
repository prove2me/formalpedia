-- Prove2me | solution 1 for WassersteinDRO.Gelbrich.gelbrich_hull_containment
-- status  : ACCEPTED   (disprove)
-- author  : @moona3k
-- created : 2026-10-06T12:06:21.688854+00:00
-- url     : https://prove2.me/submissions/95c3d692-e3b5-4de0-b528-29455b1cb19a

import Definitions.Def_WassersteinDRO_Gelbrich_ambiguitySet
import Definitions.Def_WassersteinDRO_Gelbrich_covarianceMatrix
import Definitions.Def_WassersteinDRO_Gelbrich_gelbrichHull
import Definitions.Def_WassersteinDRO_Gelbrich_meanVector
import Definitions.Def_WassersteinDRO_Gelbrich_wassersteinDistance
import Mathlib

-- Complete local proof: Solutions.Gelbrich_CounterAlgebra
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace GelbrichCodex

def candidateCovariance : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 3 / 2], ![3 / 2, 1]]

lemma candidateCovariance_not_psd : ¬ candidateCovariance.PosSemidef := by
  intro h
  have hv := h.dotProduct_mulVec_nonneg (![1,-1] : Fin 2 → ℝ)
  norm_num [candidateCovariance, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hv

lemma weight_nonnegative (n : ℕ) : 0 ≤ (3 / 8 : ℝ) * (1 / 4 : ℝ) ^ n := by positivity

lemma weight_first (n : ℕ) :
    ((3 / 8 : ℝ) * (1 / 4 : ℝ) ^ n) * (2 : ℝ) ^ n =
      (3 / 8 : ℝ) * (1 / 2 : ℝ) ^ n := by
  rw [mul_assoc, ← mul_pow]
  norm_num

lemma weight_square (n : ℕ) :
    ((3 / 8 : ℝ) * (1 / 4 : ℝ) ^ n) * ((2 : ℝ) ^ n) ^ 2 = 3 / 8 := by
  rw [← pow_mul, mul_comm n 2, pow_mul, mul_assoc, ← mul_pow]
  norm_num

#print axioms candidateCovariance_not_psd
#print axioms weight_nonnegative
#print axioms weight_first
#print axioms weight_square
end GelbrichCodex

-- Complete local proof: Solutions.Gelbrich_GeometricWeights
set_option autoImplicit false
noncomputable section
namespace GelbrichCodex

def weight (n : ℕ) : ℝ := (3 / 8 : ℝ) * (1 / 4 : ℝ) ^ n

lemma hasSum_weight : HasSum weight (1 / 2 : ℝ) := by
  have h := (hasSum_geometric_of_abs_lt_one (by norm_num : |(1 / 4 : ℝ)| < 1)).mul_left (3 / 8 : ℝ)
  convert h using 1 <;> (first | rfl | norm_num [weight])

lemma hasSum_weight_first : HasSum (fun n => weight n * (2 : ℝ) ^ n) (3 / 4 : ℝ) := by
  have h := (hasSum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left (3 / 8 : ℝ)
  have he : (fun n => weight n * (2 : ℝ) ^ n) = (fun n => (3 / 8 : ℝ) * (1 / 2 : ℝ) ^ n) := by
    funext n
    exact weight_first n
  rw [he]
  convert h using 1 <;> (first | rfl | norm_num)

lemma ennreal_weight_sum : (∑' n, ENNReal.ofReal (weight n)) = ENNReal.ofReal (1 / 2 : ℝ) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (f := weight) (fun n => weight_nonnegative n) hasSum_weight.summable,
    hasSum_weight.tsum_eq]

#print axioms hasSum_weight
#print axioms hasSum_weight_first
#print axioms ennreal_weight_sum
end GelbrichCodex

-- Complete local proof: Solutions.Gelbrich_SymmetricMeasure
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace GelbrichCodex
abbrev Space := EuclideanSpace ℝ (Fin 2)
def atom (n : ℕ) : Space := WithLp.toLp 2 ![(2 : ℝ)^n, 1]
def positiveMeasure : Measure Space :=
  Measure.sum (fun n => ENNReal.ofReal (weight n) • Measure.dirac (atom n))
def negativeMeasure : Measure Space :=
  Measure.sum (fun n => ENNReal.ofReal (weight n) • Measure.dirac (-atom n))
def counterMeasure : Measure Space := positiveMeasure + negativeMeasure

lemma positiveMeasure_univ : positiveMeasure Set.univ = ENNReal.ofReal (1/2 : ℝ) := by
  unfold positiveMeasure
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact ennreal_weight_sum
lemma negativeMeasure_univ : negativeMeasure Set.univ = ENNReal.ofReal (1/2 : ℝ) := by
  unfold negativeMeasure
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact ennreal_weight_sum
lemma counterMeasure_probability : IsProbabilityMeasure counterMeasure := by
  constructor
  rw [counterMeasure, Measure.add_apply, positiveMeasure_univ, negativeMeasure_univ,
    ← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)]
  norm_num

lemma positiveMeasure_map_neg : positiveMeasure.map (fun x : Space => -x) = negativeMeasure := by
  unfold positiveMeasure negativeMeasure
  rw [Measure.map_sum measurable_neg.aemeasurable]
  congr 1
  funext n
  rw [Measure.map_smul, Measure.map_dirac' measurable_neg]
lemma negativeMeasure_map_neg : negativeMeasure.map (fun x : Space => -x) = positiveMeasure := by
  unfold positiveMeasure negativeMeasure
  rw [Measure.map_sum measurable_neg.aemeasurable]
  congr 1
  funext n
  rw [Measure.map_smul, Measure.map_dirac' measurable_neg]
  simp only [neg_neg]
lemma counterMeasure_map_neg : counterMeasure.map (fun x : Space => -x) = counterMeasure := by
  rw [counterMeasure, Measure.map_add _ _ measurable_neg, positiveMeasure_map_neg,
    negativeMeasure_map_neg, add_comm]
lemma counterMeasure_mean_zero : WassersteinDRO.Gelbrich.meanVector counterMeasure = 0 := by
  unfold WassersteinDRO.Gelbrich.meanVector
  have he : (∫ x : Space, x ∂counterMeasure) = -(∫ x : Space, x ∂counterMeasure) := by
    calc
      _ = ∫ x : Space, x ∂counterMeasure.map (fun x : Space => -x) := by rw [counterMeasure_map_neg]
      _ = ∫ x : Space, -x ∂counterMeasure :=
        integral_map measurable_neg.aemeasurable aestronglyMeasurable_id
      _ = _ := integral_neg _
  have hz : (2 : ℝ) • (∫ x : Space, x ∂counterMeasure) = 0 := by
    simpa only [two_smul] using (eq_neg_iff_add_eq_zero.mp he)
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

#print axioms positiveMeasure_univ
#print axioms negativeMeasure_univ
#print axioms counterMeasure_probability
#print axioms positiveMeasure_map_neg
#print axioms negativeMeasure_map_neg
#print axioms counterMeasure_map_neg
#print axioms counterMeasure_mean_zero
end GelbrichCodex

-- Complete local proof: Solutions.Gelbrich_MomentIntegrals
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace GelbrichCodex
lemma atom_zero (n : ℕ) : atom n 0 = (2 : ℝ)^n := rfl
lemma atom_one (n : ℕ) : atom n 1 = (1 : ℝ) := rfl
lemma weight_toReal (n : ℕ) : (ENNReal.ofReal (weight n)).toReal = weight n :=
  ENNReal.toReal_ofReal (weight_nonnegative n)

lemma positive_integrable_scalar (f : Space → ℝ)
    (h : Summable (fun n => weight n * ‖f (atom n)‖)) : Integrable f positiveMeasure := by
  unfold positiveMeasure
  apply integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top)
  simpa only [weight_toReal] using h
lemma negative_integrable_scalar (f : Space → ℝ)
    (h : Summable (fun n => weight n * ‖f (-atom n)‖)) : Integrable f negativeMeasure := by
  unfold negativeMeasure
  apply integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top)
  simpa only [weight_toReal] using h
lemma positive_integral_scalar (f : Space → ℝ) :
    (∫ x, f x ∂positiveMeasure) = ∑' n, weight n * f (atom n) := by
  unfold positiveMeasure
  rw [integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top)]
  simp only [weight_toReal, smul_eq_mul]
lemma negative_integral_scalar (f : Space → ℝ) :
    (∫ x, f x ∂negativeMeasure) = ∑' n, weight n * f (-atom n) := by
  unfold negativeMeasure
  rw [integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top)]
  simp only [weight_toReal, smul_eq_mul]

lemma positive_first_square_not_integrable : ¬ Integrable (fun x : Space => (x 0)^2) positiveMeasure := by
  intro h
  unfold positiveMeasure at h
  have hs := h.summable_of_dirac
  have he : (fun n : ℕ => (ENNReal.ofReal (weight n)).toReal * ‖(atom n 0)^2‖) =
      (fun _ : ℕ => (3/8 : ℝ)) := by
    funext n
    rw [weight_toReal, atom_zero, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact weight_square n
  rw [he] at hs
  have hz : (3/8 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hs.tendsto_atTop_zero
  norm_num at hz
lemma counter_first_square_not_integrable : ¬ Integrable (fun x : Space => (x 0)^2) counterMeasure := by
  intro h
  apply positive_first_square_not_integrable
  apply h.mono_measure
  change positiveMeasure ≤ positiveMeasure + negativeMeasure
  exact Measure.le_add_right le_rfl
lemma counter_first_square_integral : (∫ x : Space, (x 0)^2 ∂counterMeasure) = 0 :=
  integral_undef counter_first_square_not_integrable

lemma positive_cross_integrable : Integrable (fun x : Space => x 0 * x 1) positiveMeasure := by
  apply positive_integrable_scalar
  simpa [atom, Real.norm_eq_abs, abs_pow] using hasSum_weight_first.summable
lemma negative_cross_integrable : Integrable (fun x : Space => x 0 * x 1) negativeMeasure := by
  apply negative_integrable_scalar
  simpa [atom, Real.norm_eq_abs, abs_pow] using hasSum_weight_first.summable
lemma counter_cross_integral : (∫ x : Space, x 0 * x 1 ∂counterMeasure) = 3/2 := by
  rw [counterMeasure, integral_add_measure positive_cross_integrable negative_cross_integrable,
    positive_integral_scalar, negative_integral_scalar]
  have hp : (fun n : ℕ => weight n * (atom n 0 * atom n 1)) = (fun n => weight n * (2 : ℝ)^n) := by
    funext n
    simp [atom]
  have hn : (fun n : ℕ => weight n * ((-atom n) 0 * (-atom n) 1)) = (fun n => weight n * (2 : ℝ)^n) := by
    funext n
    simp [atom]
  rw [hp, hn, hasSum_weight_first.tsum_eq]
  norm_num
lemma positive_second_square_integrable : Integrable (fun x : Space => (x 1)^2) positiveMeasure := by
  apply positive_integrable_scalar
  simpa [atom] using hasSum_weight.summable
lemma negative_second_square_integrable : Integrable (fun x : Space => (x 1)^2) negativeMeasure := by
  apply negative_integrable_scalar
  simpa [atom] using hasSum_weight.summable
lemma counter_second_square_integral : (∫ x : Space, (x 1)^2 ∂counterMeasure) = 1 := by
  rw [counterMeasure, integral_add_measure positive_second_square_integrable negative_second_square_integrable,
    positive_integral_scalar, negative_integral_scalar]
  have hp : (fun n : ℕ => weight n * (atom n 1)^2) = weight := by funext n; simp [atom]
  have hn : (fun n : ℕ => weight n * ((-atom n) 1)^2) = weight := by funext n; simp [atom]
  rw [hp, hn, hasSum_weight.tsum_eq]
  norm_num

#print axioms atom_zero
#print axioms atom_one
#print axioms weight_toReal
#print axioms positive_integrable_scalar
#print axioms negative_integrable_scalar
#print axioms positive_integral_scalar
#print axioms negative_integral_scalar
#print axioms positive_first_square_not_integrable
#print axioms counter_first_square_not_integrable
#print axioms counter_first_square_integral
#print axioms positive_cross_integrable
#print axioms negative_cross_integrable
#print axioms counter_cross_integral
#print axioms positive_second_square_integrable
#print axioms negative_second_square_integrable
#print axioms counter_second_square_integral
end GelbrichCodex

-- Complete local proof: Solutions.Gelbrich_Covariance
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace GelbrichCodex
lemma counter_covariance : WassersteinDRO.Gelbrich.covarianceMatrix counterMeasure = candidateCovariance := by
  have hzero : (∫ x : Space, x 0 * x 0 ∂counterMeasure) = 0 := by
    simpa only [pow_two] using counter_first_square_integral
  have hone : (∫ x : Space, x 1 * x 1 ∂counterMeasure) = 1 := by
    simpa only [pow_two] using counter_second_square_integral
  have hrev : (∫ x : Space, x 1 * x 0 ∂counterMeasure) = 3/2 := by
    simpa only [mul_comm] using counter_cross_integral
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [WassersteinDRO.Gelbrich.covarianceMatrix, counterMeasure_mean_zero, candidateCovariance] using hzero
  · simpa [WassersteinDRO.Gelbrich.covarianceMatrix, counterMeasure_mean_zero, candidateCovariance] using counter_cross_integral
  · simpa [WassersteinDRO.Gelbrich.covarianceMatrix, counterMeasure_mean_zero, candidateCovariance] using hrev
  · simpa [WassersteinDRO.Gelbrich.covarianceMatrix, counterMeasure_mean_zero, candidateCovariance] using hone
lemma counter_covariance_not_psd : ¬ (WassersteinDRO.Gelbrich.covarianceMatrix counterMeasure).PosSemidef := by
  rw [counter_covariance]
  exact candidateCovariance_not_psd
#print axioms counter_covariance
#print axioms counter_covariance_not_psd
end GelbrichCodex

-- Complete local proof: Solutions.Gelbrich_SelfTransport
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace GelbrichCodex
lemma wasserstein_self_two (Q : Measure Space) :
    WassersteinDRO.Gelbrich.wassersteinDistance 2 Q Q = 0 := by
  let π := Q.map (fun x : Space => (x,x))
  have hd : Measurable (fun x : Space => (x,x)) := by fun_prop
  have hf : π.map Prod.fst = Q := by
    dsimp [π]
    rw [Measure.map_map measurable_fst hd]
    exact Measure.map_id'
  have hs : π.map Prod.snd = Q := by
    dsimp [π]
    rw [Measure.map_map measurable_snd hd]
    exact Measure.map_id'
  have hg : Measurable (fun z : Space × Space => ENNReal.ofReal (‖z.1-z.2‖^(2 : ℝ))) := by
    fun_prop
  have hc : (∫⁻ z : Space × Space, ENNReal.ofReal (‖z.1-z.2‖^(2 : ℝ)) ∂π) = 0 := by
    dsimp [π]
    rw [lintegral_map hg hd]
    norm_num
  unfold WassersteinDRO.Gelbrich.wassersteinDistance
  have he : (⨅ (ρ : Measure (Space × Space)) (_ : ρ.map Prod.fst = Q ∧ ρ.map Prod.snd = Q),
      ∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖^(2 : ℝ)) ∂ρ) = 0 := by
    apply le_antisymm
    · exact iInf_le_of_le π (iInf_le_of_le ⟨hf,hs⟩ (le_of_eq hc))
    · exact zero_le
  rw [he]
  exact ENNReal.zero_rpow_of_pos (by norm_num)
#print axioms wasserstein_self_two
end GelbrichCodex

-- Complete local proof: Solutions.Dis_WassersteinDRO_Gelbrich_gelbrich_hull_containment
set_option autoImplicit false
open MeasureTheory WassersteinDRO.Gelbrich
noncomputable section
namespace GelbrichCodex
lemma counter_in_ambiguity : counterMeasure ∈ ambiguitySet 0 2 Set.univ counterMeasure := by
  letI := counterMeasure_probability
  refine ⟨measure_univ, by simp, ?_⟩
  rw [wasserstein_self_two]
  norm_num
lemma counter_not_in_hull (ε : ℝ) (μ : Space) (Sigma : Matrix (Fin 2) (Fin 2) ℝ) :
    counterMeasure ∉ gelbrichHull ε Set.univ μ Sigma := by
  intro h
  exact counter_covariance_not_psd h.2.2.1
#print axioms counter_in_ambiguity
#print axioms counter_not_in_hull
end GelbrichCodex

theorem solution : ¬ (∀ {m : ℕ} (ε p : ℝ) (hp : 2 ≤ p)
    (Ξ : Set (EuclideanSpace ℝ (Fin m))) (PN : Measure (EuclideanSpace ℝ (Fin m)))
    (μhat : EuclideanSpace ℝ (Fin m)) (SigmaHat : Matrix (Fin m) (Fin m) ℝ)
    (hμ : meanVector PN = μhat) (hS : covarianceMatrix PN = SigmaHat),
    ambiguitySet ε p Ξ PN ⊆ gelbrichHull ε Ξ μhat SigmaHat) := by
  intro h
  have hs := h (m := 2) 0 2 (by norm_num) Set.univ GelbrichCodex.counterMeasure
    (meanVector GelbrichCodex.counterMeasure) (covarianceMatrix GelbrichCodex.counterMeasure) rfl rfl
  exact GelbrichCodex.counter_not_in_hull 0 _ _ (hs GelbrichCodex.counter_in_ambiguity)

#print axioms solution
