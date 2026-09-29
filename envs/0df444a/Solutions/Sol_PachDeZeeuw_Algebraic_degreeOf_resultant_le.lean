-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.degreeOf_resultant_le
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:52.978971+00:00
-- url     : https://prove2.me/submissions/18997470-40b7-4606-a336-83a67f04c09d

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve
namespace PachDeZeeuw.Algebraic

/-- The `degreeOf 0` of any coefficient of `Curry0 p` is bounded by `degreeOf 1 p`. -/
lemma degreeOf_coeff_curry0_le (p : MvPolynomial (Fin 2) ℝ) (k : ℕ) :
    MvPolynomial.degreeOf (0 : Fin 1) ((Curry0 p).coeff k) ≤ MvPolynomial.degreeOf (1 : Fin 2) p := by
  simpa [Curry0] using
    (MvPolynomial.degreeOf_coeff_finSuccEquiv (R := ℝ) (n := 1) (p := p) (j := 0) (i := k))

/-- Each Sylvester matrix entry is, in `degreeOf 0`, bounded by `max d₁ d₂`.

This is the kernel-cheap bound: every entry is either `0`, a coefficient of `Curry0 p`,
or a coefficient of `Curry0 q`, and `degreeOf 0` of any such is `≤ max d₁ d₂`. We avoid
unfolding the Sylvester determinant in the kernel by reducing the entry with
`Matrix.of_apply` and casing the column index through `Fin.addCases`. -/
lemma degreeOf_sylvester_entry_bound
    (p q : MvPolynomial (Fin 2) ℝ)
    {d₁ d₂ : ℕ}
    (i j : Fin ((Curry0 p).natDegree + (Curry0 q).natDegree))
    (hpdeg : p.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂) :
    MvPolynomial.degreeOf (0 : Fin 1)
      (Polynomial.sylvester (Curry0 p) (Curry0 q)
        (Curry0 p).natDegree (Curry0 q).natDegree i j) ≤ max d₁ d₂ := by
  classical
  have hpbound : ∀ k : ℕ, MvPolynomial.degreeOf (0 : Fin 1) ((Curry0 p).coeff k) ≤ max d₁ d₂ := by
    intro k
    exact le_trans (degreeOf_coeff_curry0_le p k)
      (le_trans (MvPolynomial.degreeOf_le_totalDegree p 1) (le_trans hpdeg (le_max_left _ _)))
  have hqbound : ∀ k : ℕ, MvPolynomial.degreeOf (0 : Fin 1) ((Curry0 q).coeff k) ≤ max d₁ d₂ := by
    intro k
    exact le_trans (degreeOf_coeff_curry0_le q k)
      (le_trans (MvPolynomial.degreeOf_le_totalDegree q 1) (le_trans hqdeg (le_max_right _ _)))
  refine Fin.addCases (motive := fun j =>
      MvPolynomial.degreeOf (0 : Fin 1)
        (Polynomial.sylvester (Curry0 p) (Curry0 q)
          (Curry0 p).natDegree (Curry0 q).natDegree i j) ≤ max d₁ d₂) ?_ ?_ j
  · intro jl
    rw [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    by_cases hmem : (i : ℕ) ∈ Set.Icc (jl : ℕ) ((jl : ℕ) + (Curry0 q).natDegree)
    · rw [if_pos hmem]; exact hqbound _
    · rw [if_neg hmem]; exact Nat.zero_le _
  · intro jr
    rw [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    by_cases hmem : (i : ℕ) ∈ Set.Icc (jr : ℕ) ((jr : ℕ) + (Curry0 p).natDegree)
    · rw [if_pos hmem]; exact hpbound _
    · rw [if_neg hmem]; exact Nat.zero_le _

end PachDeZeeuw.Algebraic

open PachDeZeeuw.Algebraic in
theorem solution (p q : MvPolynomial (Fin 2) ℝ)
    {d₁ d₂ : ℕ}
    (hpdeg : p.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂) :
    MvPolynomial.degreeOf (0 : Fin 1) (ResultantCoeff p q) ≤ (d₁ + d₂) ^ 2 := by
  classical
  set m := (Curry0 p).natDegree with hm_def
  set n := (Curry0 q).natDegree with hn_def
  have hm : m ≤ d₁ := by
    rw [hm_def]
    calc
      (Curry0 p).natDegree = MvPolynomial.degreeOf (0 : Fin 2) p := by
        simpa [Curry0] using
          (MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := 1) (f := p))
      _ ≤ p.totalDegree := MvPolynomial.degreeOf_le_totalDegree p 0
      _ ≤ d₁ := hpdeg
  have hn : n ≤ d₂ := by
    rw [hn_def]
    calc
      (Curry0 q).natDegree = MvPolynomial.degreeOf (0 : Fin 2) q := by
        simpa [Curry0] using
          (MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := 1) (f := q))
      _ ≤ q.totalDegree := MvPolynomial.degreeOf_le_totalDegree q 0
      _ ≤ d₂ := hqdeg
  rw [ResultantCoeff, Polynomial.resultant, Matrix.det_apply]
  refine le_trans (MvPolynomial.degreeOf_sum_le (0 : Fin 1) Finset.univ _) ?_
  refine Finset.sup_le ?_
  intro σ hσ
  have hsign :
      MvPolynomial.degreeOf (0 : Fin 1)
        (Equiv.Perm.sign σ • ∏ i, Polynomial.sylvester (Curry0 p) (Curry0 q)
          (Curry0 p).natDegree (Curry0 q).natDegree (σ i) i) ≤
      MvPolynomial.degreeOf (0 : Fin 1)
        (∏ i, Polynomial.sylvester (Curry0 p) (Curry0 q)
          (Curry0 p).natDegree (Curry0 q).natDegree (σ i) i) := by
    rw [Units.smul_def, zsmul_eq_mul]
    simpa using
      (MvPolynomial.degreeOf_C_mul_le
        (∏ i, Polynomial.sylvester (Curry0 p) (Curry0 q)
          (Curry0 p).natDegree (Curry0 q).natDegree (σ i) i) 0
        ((Equiv.Perm.sign σ : ℤ) : ℝ))
  have hprod :
      MvPolynomial.degreeOf (0 : Fin 1)
        (∏ i, Polynomial.sylvester (Curry0 p) (Curry0 q)
          (Curry0 p).natDegree (Curry0 q).natDegree (σ i) i) ≤
      ∑ _i : Fin (m + n), max d₁ d₂ := by
    refine le_trans (by
      simpa using
        (MvPolynomial.degreeOf_prod_le (0 : Fin 1) Finset.univ
          (fun i : Fin (m + n) =>
            Polynomial.sylvester (Curry0 p) (Curry0 q)
              (Curry0 p).natDegree (Curry0 q).natDegree (σ i) i))) ?_
    refine Finset.sum_le_sum ?_
    intro i hi
    exact degreeOf_sylvester_entry_bound p q (σ i) i hpdeg hqdeg
  have hsum : (∑ _i : Fin (m + n), max d₁ d₂) = (m + n) * max d₁ d₂ := by
    simp [Finset.sum_const, Finset.card_univ]
  have hmn : (m + n) * max d₁ d₂ ≤ (d₁ + d₂) ^ 2 := by
    have hmn_le : m + n ≤ d₁ + d₂ := Nat.add_le_add hm hn
    have hmax_le : max d₁ d₂ ≤ d₁ + d₂ := max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    calc
      (m + n) * max d₁ d₂ ≤ (d₁ + d₂) * (d₁ + d₂) :=
        Nat.mul_le_mul hmn_le hmax_le
      _ = (d₁ + d₂) ^ 2 := by rw [pow_two]
  have hprod' :
      MvPolynomial.degreeOf (0 : Fin 1)
        (∏ i, Polynomial.sylvester (Curry0 p) (Curry0 q)
          (Curry0 p).natDegree (Curry0 q).natDegree (σ i) i) ≤
      (d₁ + d₂) ^ 2 := by
    refine le_trans hprod ?_
    rw [hsum]; exact hmn
  exact le_trans hsign hprod'
