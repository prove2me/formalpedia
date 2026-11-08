-- Prove2me | solution 1 for WHMultiplicativity.isChannel_wernerHolevo
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:30:57.035733+00:00
-- url     : https://prove2.me/submissions/c5fa2ea8-3aad-49d5-86fd-b5c3c99e1e33

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WHAdditivity_Renyi_Model

open WHAdditivity.Renyi
open scoped Matrix

namespace Aux_WHisChannel

noncomputable def E (d : ℕ) (c : ℂ) (p : Fin d × Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun a b => c * ((if a = p.1 then 1 else 0) * (if b = p.2 then 1 else 0)
    - (if a = p.2 then 1 else 0) * (if b = p.1 then 1 else 0))

lemma kraus (d : ℕ) (c : ℂ) (hc : 2 * (starRingEnd ℂ c * c) * ((d : ℂ) - 1) = 1) :
    ∑ p : Fin d × Fin d, (E d c p)ᴴ * E d c p = 1 := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, E, Matrix.of_apply,
    Fintype.sum_prod_type]
  simp only [star_mul', star_sub, mul_sub, sub_mul, mul_ite, ite_mul, mul_one, mul_zero, one_mul,
    zero_mul, star_one, star_zero, apply_ite star, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  rw [Matrix.one_apply]
  by_cases h : a = b
  · subst h
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
    linear_combination hc
  · simp [h, Finset.sum_ite_eq, Finset.sum_ite_eq', Ne.symm h]

lemma action (d : ℕ) (c : ℂ) (hc : 2 * (starRingEnd ℂ c * c) * ((d : ℂ) - 1) = 1)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hd : ((d : ℂ) - 1) ≠ 0) :
    wernerHolevo d ρ = ∑ p : Fin d × Fin d, E d c p * ρ * (E d c p)ᴴ := by
  ext a b
  simp only [wernerHolevo, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.transpose_apply, smul_eq_mul, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, E, Matrix.of_apply, Fintype.sum_prod_type, Matrix.trace,
    Matrix.diag]
  simp only [star_mul', star_sub, mul_sub, sub_mul, mul_ite, ite_mul, mul_one, mul_zero, one_mul,
    zero_mul, star_one, star_zero, apply_ite star, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  have hc' : ((d : ℂ) - 1)⁻¹ = 2 * (starRingEnd ℂ c * c) := by
    exact (eq_inv_of_mul_eq_one_left hc).symm
  rw [hc']
  by_cases h : a = b
  · subst h
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mul_sum]
    ring_nf
    rw [Finset.sum_mul]
  · simp [h, Finset.sum_ite_eq, Finset.sum_ite_eq', Ne.symm h]
    ring

end Aux_WHisChannel

open Aux_WHisChannel in
theorem solution (d : ℕ) (hd : 2 ≤ d) :
    QAlgorithms.IsChannel (wernerHolevo d) := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  set r := Real.sqrt (2 * ((d : ℝ) - 1)) with hrdef
  have hr : r ^ 2 = 2 * ((d : ℝ) - 1) := Real.sq_sqrt (by linarith)
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by linarith)
  set c : ℂ := ((r⁻¹ : ℝ) : ℂ) with hcdef
  have hc : 2 * (starRingEnd ℂ c * c) * ((d : ℂ) - 1) = 1 := by
    rw [hcdef, Complex.conj_ofReal]
    have h1 : r⁻¹ * r⁻¹ = (2 * ((d : ℝ) - 1))⁻¹ := by rw [← hr]; ring
    have h2 : (2 : ℝ) * (r⁻¹ * r⁻¹) * ((d : ℝ) - 1) = 1 := by
      have hne : (d : ℝ) - 1 ≠ 0 := by linarith
      rw [h1]; field_simp
    exact_mod_cast h2
  have hdC : (d : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast (by omega : d ≠ 1)
  refine ⟨d * d, fun k => E d c (finProdFinEquiv.symm k), ?_, ?_⟩
  · unfold QAlgorithms.IsKrausFamily
    rw [Equiv.sum_comp finProdFinEquiv.symm (fun p => (E d c p)ᴴ * E d c p)]
    exact kraus d c hc
  · intro ρ
    unfold QAlgorithms.krausApply
    rw [Equiv.sum_comp finProdFinEquiv.symm (fun p => E d c p * ρ * (E d c p)ᴴ)]
    exact action d c hc ρ hdC
