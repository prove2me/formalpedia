-- Prove2me | solution 1 for PolySampIso.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:40:41.068717+00:00
-- url     : https://prove2.me/submissions/08c0ff02-432e-4cce-992c-b26ca0ef2e96

import Mathlib
import Definitions.Def_PolySampIso_LogBarrier
import Definitions.Def_PolySampIso_LLT
import Definitions.Def_PolySampIso_Forwards

open MeasureTheory

namespace Aux_PolySampIso_l2
open PolySampIso

lemma meas_exp_inner {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun y : EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (Real.exp (inner ℝ x y))) := by
  apply ENNReal.measurable_ofReal.comp
  exact (Real.continuous_exp.comp (continuous_const.inner continuous_id)).measurable

lemma laplace_conv {d : ℕ} (μ ν : Measure (EuclideanSpace ℝ (Fin d))) [SFinite ν]
    (x : EuclideanSpace ℝ (Fin d)) : laplace (μ ∗ ν) x = laplace μ x * laplace ν x := by
  unfold laplace
  rw [Measure.lintegral_conv (meas_exp_inner x)]
  have e : ∀ y z : EuclideanSpace ℝ (Fin d), ENNReal.ofReal (Real.exp (inner ℝ x (y + z)))
      = ENNReal.ofReal (Real.exp (inner ℝ x y)) * ENNReal.ofReal (Real.exp (inner ℝ x z)) := by
    intro y z
    rw [inner_add_right, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp_rw [e]
  simp_rw [lintegral_const_mul _ (meas_exp_inner x)]
  rw [lintegral_mul_const _ (meas_exp_inner x)]

lemma laplace_dirac {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    laplace (Measure.dirac 0) x = 1 := by
  unfold laplace
  rw [lintegral_dirac' _ (meas_exp_inner x)]
  simp

lemma laplace_foldr {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    ∀ L : List (Measure (EuclideanSpace ℝ (Fin d))), (∀ μ ∈ L, SFinite μ) →
      SFinite (L.foldr (· ∗ ·) (Measure.dirac 0)) ∧
      laplace (L.foldr (· ∗ ·) (Measure.dirac 0)) x = (L.map (fun μ => laplace μ x)).prod := by
  intro L
  induction L with
  | nil =>
    intro _
    simp only [List.foldr_nil, List.map_nil, List.prod_nil]
    exact ⟨inferInstance, laplace_dirac x⟩
  | cons μ L ih =>
    intro h
    obtain ⟨h1, h2⟩ := ih (fun ν hν => h ν (List.mem_cons_of_mem _ hν))
    haveI : SFinite μ := h μ List.mem_cons_self
    haveI := h1
    refine ⟨?_, ?_⟩
    · simp only [List.foldr_cons]; infer_instance
    · simp only [List.foldr_cons, List.map_cons, List.prod_cons]
      rw [laplace_conv, h2]

lemma facet_sfinite {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (i : Fin m) :
    SFinite (facetMeasure A b i) := by
  unfold facetMeasure; infer_instance

lemma inner_row {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m)
    (x : EuclideanSpace ℝ (Fin n)) : inner ℝ x (rowVec A i) = ∑ j, A i j * x j := by
  unfold rowVec
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp [mul_comm]

lemma laplace_facet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (i : Fin m)
    (x : EuclideanSpace ℝ (Fin n)) (hs : 0 < slack A b x i) :
    laplace (facetMeasure A b i) x = ENNReal.ofReal (1 / slack A b x i) := by
  unfold laplace facetMeasure
  have hmeas : Measurable (fun t : ℝ => t • rowVec A i) :=
    (continuous_id.smul continuous_const).measurable
  rw [lintegral_map (meas_exp_inner x) hmeas]
  have hdens : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-t * b i))) := by
    apply ENNReal.measurable_ofReal.comp
    exact (Real.continuous_exp.comp ((continuous_neg.mul continuous_const))).measurable
  have hg : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (inner ℝ x (t • rowVec A i)))) :=
    (meas_exp_inner x).comp hmeas
  rw [lintegral_withDensity_eq_lintegral_mul _ hdens hg]
  set s := slack A b x i with hsdef
  have e : ∀ t : ℝ, ((fun t : ℝ => ENNReal.ofReal (Real.exp (-t * b i))) *
      (fun t : ℝ => ENNReal.ofReal (Real.exp (inner ℝ x (t • rowVec A i))))) t
      = ENNReal.ofReal (Real.exp ((-s) * t)) := by
    intro t
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, inner_smul_right, inner_row]
    congr 2
    rw [hsdef]; unfold slack; ring
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi (by linarith) 0)
    (Filter.Eventually.of_forall (fun t => (Real.exp_pos _).le)),
    integral_exp_mul_Ioi (by linarith) 0]
  congr 1
  rw [mul_zero, Real.exp_zero]
  field_simp

end Aux_PolySampIso_l2

open PolySampIso Aux_PolySampIso_l2 in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hX : StandingAssumption A b) (hn : 0 < n) :
    IsLLTOn (dualMeasure A b) (logBarrier A b) (polytope A b) := by
  intro x hx
  have hs : ∀ i, 0 < slack A b x i := fun i => by
    unfold slack; have := hx i; linarith
  unfold dualMeasure
  rw [(laplace_foldr x (List.ofFn (facetMeasure A b)) (fun μ hμ => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hμ
    exact facet_sfinite A b i)).2]
  rw [List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply]
  rw [Finset.prod_congr rfl (fun i _ => laplace_facet A b i x (hs i))]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (one_div_pos.2 (hs i)).le)]
  congr 1
  unfold logBarrier
  rw [Real.exp_neg, Real.exp_sum]
  rw [Finset.prod_congr rfl (fun i _ => Real.exp_log (hs i))]
  rw [← Finset.prod_inv_distrib]
  simp [one_div]
