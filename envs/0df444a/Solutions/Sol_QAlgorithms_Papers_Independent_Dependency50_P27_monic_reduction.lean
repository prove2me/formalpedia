-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P27.monic_reduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:30:13.457625+00:00
-- url     : https://prove2.me/submissions/771d5e9c-584f-4e94-8945-ac03044d3348

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P27
open Polynomial

lemma S170bK_sign {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (l x : R) (q : Polynomial R) :
    (signTransform l q).eval (l * x) = l ^ (2 * q.natDegree) * q.eval x := by
  unfold signTransform
  rw [Polynomial.eval_finset_sum, Polynomial.eval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Polynomial.eval_monomial, mul_pow]
  have : l ^ (2 * q.natDegree) = l ^ (2 * q.natDegree - i) * l ^ i := by
    rw [← pow_add]; congr 1; omega
  rw [this]; ring


theorem solution {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : Polynomial R) (qs : List (Polynomial R))
    (hdegree : 1 ≤ p.natDegree) :
    (monicTransform p).Monic ∧
    (monicTransform p).comp (C p.leadingCoeff * X) =
      C (p.leadingCoeff ^ (p.natDegree - 1)) * p ∧
    (feasible p qs ↔ feasible (monicTransform p) (qs.map (signTransform p.leadingCoeff))) := by
  set d := p.natDegree with hd
  set l := p.leadingCoeff with hl
  have hp0 : p ≠ 0 := by rintro rfl; simp [d] at hdegree
  have hl0 : l ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hp0
  have hdeg : (∑ i ∈ Finset.range d, Polynomial.monomial i (p.coeff i * l ^ (d - 1 - i))).degree < d := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    rw [Polynomial.finset_sum_coeff]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [Polynomial.coeff_monomial, if_neg (by omega)]
  have hcomp : (monicTransform p).comp (Polynomial.C l * Polynomial.X) = Polynomial.C (l ^ (d - 1)) * p := by
    unfold monicTransform
    rw [← hd, ← hl]
    conv_rhs => rw [p.as_sum_range_C_mul_X_pow, ← hd, Finset.mul_sum, Finset.sum_range_succ]
    rw [Polynomial.add_comp, Polynomial.sum_comp, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [Polynomial.monomial_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul,
        ← mul_assoc, ← Polynomial.C_mul]
      congr 2
      have : l ^ (d - 1) = l ^ (d - 1 - i) * l ^ i := by rw [← pow_add]; congr 1; omega
      rw [this]; ring
    · rw [Polynomial.X_pow_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul,
        Polynomial.coeff_natDegree, ← hl, ← pow_succ, Nat.sub_add_cancel hdegree]
  have hev : ∀ x, (monicTransform p).eval (l * x) = l ^ (d - 1) * p.eval x := by
    intro x
    have := congrArg (Polynomial.eval x) hcomp
    simpa [Polynomial.eval_comp] using this
  refine ⟨Polynomial.monic_X_pow_add hdeg, hcomp, ?_⟩
  have hpos : ∀ q : Polynomial R, 0 < l ^ (2 * q.natDegree) := fun q => by
    rw [pow_mul]; exact pow_pos (by positivity) _
  constructor
  · rintro ⟨x, hx, hq⟩
    refine ⟨l * x, by rw [hev, hx, mul_zero], fun q' hq' => ?_⟩
    obtain ⟨q, hqm, rfl⟩ := List.mem_map.1 hq'
    rw [S170bK_sign]; exact mul_pos (hpos q) (hq q hqm)
  · rintro ⟨y, hy, hq⟩
    refine ⟨y / l, ?_, fun q hqm => ?_⟩
    · have := hev (y / l)
      rw [mul_div_cancel₀ y hl0, hy] at this
      exact (mul_eq_zero.1 this.symm).resolve_left (pow_ne_zero _ hl0)
    · have h1 := hq _ (List.mem_map_of_mem hqm)
      rw [← mul_div_cancel₀ y hl0, S170bK_sign] at h1
      exact pos_of_mul_pos_right h1 (hpos q).le

end
