-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.totalDegree_pderiv_le_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:59.205381+00:00
-- url     : https://prove2.me/submissions/8a0e7abc-89e8-4154-b79e-b22580d9c10d

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve
namespace PachDeZeeuw.Algebraic

/-- A simple arithmetic helper for the derivative-degree argument. -/
lemma helper_sum_sub_single_le (v : Fin 2 →₀ ℕ) (i : Fin 2) (hvi : v i ≠ 0) :
    ((v - Finsupp.single i 1).sum (fun _ e => e)) ≤ ((v.sum (fun _ e => e)) - 1) := by
  fin_cases i
  · have h0 : 1 ≤ v 0 := Nat.pos_of_ne_zero hvi
    simp [Finsupp.sum_fintype]
    omega
  · have h1 : 1 ≤ v 1 := Nat.pos_of_ne_zero hvi
    simp [Finsupp.sum_fintype]
    omega

end PachDeZeeuw.Algebraic

open PachDeZeeuw.Algebraic in
theorem solution (h : MvPolynomial (Fin 2) ℝ) (i : Fin 2)
    (_hpos : 0 < h.totalDegree) :
    (MvPolynomial.pderiv i h).totalDegree ≤ h.totalDegree - 1 := by
  classical
  let s : Finset (Fin 2 →₀ ℕ) := h.support
  let c : (Fin 2 →₀ ℕ) → ℝ := fun v => MvPolynomial.coeff v h
  have hsum : h = ∑ v ∈ s, MvPolynomial.monomial v (c v) := by
    subst s c
    exact MvPolynomial.as_sum h
  have hderiv :
      MvPolynomial.pderiv i h = ∑ v ∈ s, MvPolynomial.pderiv i (MvPolynomial.monomial v (c v)) := by
    rw [hsum]
    simp
  have hterm : ∀ v ∈ s, (MvPolynomial.pderiv i (MvPolynomial.monomial v (c v))).totalDegree ≤
      h.totalDegree - 1 := by
    intro v hv
    by_cases hvi : v i = 0
    · simp [hvi]
    · have hcoeff : (c v) * (v i : ℝ) ≠ 0 := by
        exact mul_ne_zero
          (by simpa [c] using (MvPolynomial.mem_support_iff.mp hv))
          (by exact_mod_cast hvi)
      rw [MvPolynomial.pderiv_monomial, MvPolynomial.totalDegree_monomial _ hcoeff]
      have hvle : v.sum (fun _ e => e) ≤ h.totalDegree := MvPolynomial.le_totalDegree hv
      have hsumle :
          (v - Finsupp.single i 1).sum (fun _ e => e) ≤ v.sum (fun _ e => e) - 1 := by
        exact helper_sum_sub_single_le v i hvi
      have hsub : v.sum (fun _ e => e) - 1 ≤ h.totalDegree - 1 := by
        exact Nat.sub_le_sub_right hvle 1
      exact le_trans hsumle hsub
  rw [hderiv]
  exact MvPolynomial.totalDegree_finsetSum_le hterm
