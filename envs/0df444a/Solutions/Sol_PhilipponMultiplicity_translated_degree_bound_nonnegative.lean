-- Prove2me | solution 1 for PhilipponMultiplicity.translated_degree_bound_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-29T10:01:21.972256+00:00
-- url     : https://prove2.me/submissions/05dffdcb-d60b-4139-9893-e846b7a42795

import Theorems.Thm_PhilipponMultiplicity_lemma_4_5
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped BigOperators Topology
open MvPolynomial Filter
noncomputable section

namespace PhilipponMultiplicity

theorem homogeneous_eval_scale {ι : Type*} (F : MvPolynomial ι ℚ) (d : ℕ)
    (hF : F.IsHomogeneous d) (a : ℚ) (x : ι → ℚ) :
    eval (fun i => a * x i) F = a ^ d * eval x F := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, ← hF.degree_eq_sum_deg_support he]
  ring

/-- An inequality between homogeneous degree forms on positive natural
multidegrees extends to every natural multidegree, including the boundary. -/
theorem homogeneous_eval_le_on_nat_boundary {ι : Type*}
    (F Q : MvPolynomial ι ℚ) (d : ℕ)
    (hF : F.IsHomogeneous d) (hQ : Q.IsHomogeneous d) (c D : ι → ℕ)
    (hle : ∀ E : ι → ℕ, (∀ i, 1 ≤ E i) →
      eval (fun i => (E i : ℚ)) F ≤ eval (fun i => (c i * E i : ℚ)) Q) :
    eval (fun i => (D i : ℚ)) F ≤ eval (fun i => (c i * D i : ℚ)) Q := by
  let x : ℕ → ι → ℚ := fun n i => (D i : ℚ) + ((n + 1 : ℕ) : ℚ)⁻¹
  have hlim : Tendsto x atTop (𝓝 (fun i => (D i : ℚ))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have hh : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℚ)⁻¹) atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℚ))).comp
        (tendsto_add_atTop_nat 1)
    simpa only [add_zero] using tendsto_const_nhds.add hh
  have hlim' : Tendsto (fun n i => (c i : ℚ) * x n i) atTop
      (𝓝 (fun i => (c i * D i : ℚ))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_const_nhds.mul ((tendsto_pi_nhds.mp hlim) i)
  apply le_of_tendsto_of_tendsto (F.continuous_eval.tendsto _ |>.comp hlim)
    (Q.continuous_eval.tendsto _ |>.comp hlim')
  apply Filter.Eventually.of_forall
  intro n
  let E : ι → ℕ := fun i => (n + 1) * D i + 1
  have hh := mul_le_mul_of_nonneg_left (hle E (fun i => Nat.le_add_left 1 _))
    (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg (n + 1))) d)
  rw [← homogeneous_eval_scale F d hF, ← homogeneous_eval_scale Q d hQ] at hh
  have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hx (i : ι) : ((n + 1 : ℕ) : ℚ)⁻¹ * (E i : ℚ) = x n i := by
    dsimp [E, x]
    push_cast
    field_simp
  have hy (i : ι) : ((n + 1 : ℕ) : ℚ)⁻¹ * (c i * E i : ℚ) = (c i : ℚ) * x n i := by
    rw [mul_left_comm, hx]
  simpa only [Function.comp_def, hx, hy] using hh

/-- Lemma 4.5's degree comparison at arbitrary natural multidegrees. The
dimension equality supplies the common homogeneous degree in the limit. -/
theorem boundary_translation_established
    {K : Type*} [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (c : G.FactorIndex → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hbound : TranslationDegreeBound G c)
    (g : G.Point) (V : GroupSubvariety G) (D : G.FactorIndex → ℕ) :
    hilbertDegreeForm G V.carrier D ≤
      hilbertDegreeForm G (PhilipponMultiplicity.translate g V.carrier) (fun i => c i * D i) := by
  have hh := lemma_4_5 K hK G c hc hbound g V
  let F := Hilbert.degreeForm K G.factorCount G.ambient.ambientDimension (G.vanishingIdeal V.carrier)
  let Q := Hilbert.degreeForm K G.factorCount G.ambient.ambientDimension
    (G.vanishingIdeal (PhilipponMultiplicity.translate g V.carrier))
  have hF : F.IsHomogeneous (varietyDimension G V.carrier) := by
    dsimp [F, Hilbert.degreeForm, varietyDimension]
    rw [MvPolynomial.smul_eq_C_mul]
    exact (MvPolynomial.homogeneousComponent_isHomogeneous _ _).C_mul _
  have hQ : Q.IsHomogeneous (varietyDimension G V.carrier) := by
    rw [hh.1]
    dsimp [Q, Hilbert.degreeForm, varietyDimension]
    rw [MvPolynomial.smul_eq_C_mul]
    exact (MvPolynomial.homogeneousComponent_isHomogeneous _ _).C_mul _
  have hle : ∀ E : G.FactorIndex → ℕ, (∀ i, 1 ≤ E i) →
      eval (fun i => (E i : ℚ)) F ≤ eval (fun i => (c i * E i : ℚ)) Q := by
    intro E hE
    have h := hh.2 E hE
    change (Hilbert.degreeValue K G.factorCount G.ambient.ambientDimension
      (G.vanishingIdeal V.carrier) E : ℝ) ≤
      (Hilbert.degreeValue K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal (PhilipponMultiplicity.translate g V.carrier)) (fun i => c i * E i) : ℝ) at h
    exact_mod_cast h
  have h := homogeneous_eval_le_on_nat_boundary F Q (varietyDimension G V.carrier) hF hQ c D hle
  change (Hilbert.degreeValue K G.factorCount G.ambient.ambientDimension
    (G.vanishingIdeal V.carrier) D : ℝ) ≤
    (Hilbert.degreeValue K G.factorCount G.ambient.ambientDimension
      (G.vanishingIdeal (PhilipponMultiplicity.translate g V.carrier)) (fun i => c i * D i) : ℝ)
  exact_mod_cast h

end PhilipponMultiplicity
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (c : G.FactorIndex → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hbound : TranslationDegreeBound G c)
    (g : G.Point) (V : GroupSubvariety G) (D : G.FactorIndex → ℕ) :
    hilbertDegreeForm G V.carrier D ≤
      hilbertDegreeForm G (PhilipponMultiplicity.translate g V.carrier) (fun i => c i * D i) := by
  exact boundary_translation_established hK G c hc hbound g V D
