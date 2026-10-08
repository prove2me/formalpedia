-- Prove2me | solution 1 for PhilipponMultiplicity.closure_action_has_line_polynomial_degree_model
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-07T10:48:23.832059+00:00
-- url     : https://prove2.me/submissions/77cc329f-43e2-4190-94cf-b14eb8ba8ed5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_closure_action_has_finite_difference_degree_model
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_Support
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


section

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section

namespace IntegerDifferencePolynomial

/-- Bernoulli polynomials have the expected degree bound, including n = 0. -/
theorem bernoulli_degree_le (n : ℕ) : (Polynomial.bernoulli n).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [Polynomial.coeff_bernoulli, if_neg (not_le.mpr hk)]

/-- Every rational polynomial has a discrete antiderivative of degree at most
one larger, using the Bernoulli identity B_n(X+1)-B_n(X)=n X^(n-1). -/
theorem exists_antidifference (q : Polynomial ℚ) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ q.natDegree + 1 ∧
      ∀ x : ℚ, p.eval (x+1) - p.eval x = q.eval x := by
  classical
  let p : Polynomial ℚ := ∑ k ∈ Finset.range (q.natDegree+1),
    (q.coeff k / (k+1 : ℚ)) • Polynomial.bernoulli (k+1)
  refine ⟨p, ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    exact (Polynomial.natDegree_smul_le _ _).trans
      ((bernoulli_degree_le (k+1)).trans (by have := Finset.mem_range.mp hk; omega))
  · intro x
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_smul, smul_eq_mul,
      ← Finset.sum_sub_distrib]
    rw [q.eval_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    have hk : (k+1 : ℚ) ≠ 0 := by positivity
    have hb := Polynomial.bernoulli_eval_one_add (k+1) x
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hb
    rw [add_comm x 1, hb]
    field_simp
    ring

/-- A sequence on all integers is determined by its first differences and its
value at zero. The backward induction includes negative integers. -/
theorem eq_of_difference (f g : ℤ → ℚ) (hzero : f 0 = g 0)
    (hstep : ∀ n : ℤ, f (n+1) - f n = g (n+1) - g n) : f = g := by
  funext n
  induction n using Int.induction_on with
  | zero => exact hzero
  | succ n ih =>
      have hh := hstep n
      linarith
  | pred n ih =>
      have hh := hstep (-n-1)
      have he : (-(n : ℤ)-1)+1 = -(n : ℤ) := by ring
      rw [he] at hh
      linarith

/-- A rational sequence with vanishing (d+1)-st forward difference is the
evaluation of a rational polynomial of degree at most d on every integer. -/
theorem exists_polynomial (d : ℕ) (f : ℤ → ℚ)
    (h : (fwdDiff (1 : ℤ))^[d+1] f = 0) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ d ∧ ∀ t : ℤ, f t = p.eval (t : ℚ) := by
  induction d generalizing f with
  | zero =>
      have heq : f = (fun _ => f 0) := by
        apply eq_of_difference f (fun _ => f 0) rfl
        intro n
        have hh := congrFun h n
        simpa only [zero_add, Function.iterate_one, fwdDiff, Pi.zero_apply, sub_self] using hh
      refine ⟨Polynomial.C (f 0), by simp, ?_⟩
      intro t
      rw [Polynomial.eval_C]
      exact congrFun heq t
  | succ d ih =>
      have hd : (fwdDiff (1 : ℤ))^[d+1] (fwdDiff 1 f) = 0 := by
        simpa only [Function.iterate_succ_apply] using h
      obtain ⟨q, hq, hqeval⟩ := ih (fwdDiff 1 f) hd
      obtain ⟨p, hp, hpdelta⟩ := exists_antidifference q
      let P := p + Polynomial.C (f 0 - p.eval 0)
      have hP : P.natDegree ≤ d+1 := by
        exact (Polynomial.natDegree_add_le _ _).trans
          (max_le (hp.trans (Nat.add_le_add_right hq 1)) (by simp))
      have heq : f = (fun t : ℤ => P.eval (t : ℚ)) := by
        apply eq_of_difference
        · simp [P]
        · intro n
          have hn := hqeval n
          change f (n+1) - f n = q.eval (n : ℚ) at hn
          simpa only [P, Polynomial.eval_add, Polynomial.eval_C, Int.cast_add,
            Int.cast_one, add_sub_add_right_eq_sub] using hn.trans (hpdelta (n : ℚ)).symm
      refine ⟨P, hP, ?_⟩
      intro t
      exact congrFun heq t

/-- Restriction to an integral affine line intertwines lattice differences
with unit-step differences of integer sequences. -/
theorem iterate_on_line {σ : Type*} (f : (σ → ℤ) → ℚ)
    (x y : σ → ℤ) (n : ℕ) (t : ℤ) :
    (fwdDiff (1 : ℤ))^[n] (fun s : ℤ => f (fun i => x i + s * y i)) t =
      (fwdDiff y)^[n] f (fun i => x i + t * y i) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply', fwdDiff]
      rw [ih (t := t+1), ih]
      have he : (fun i => x i + (t+1) * y i) = (fun i => x i + t * y i) + y := by
        funext i
        simp only [Pi.add_apply]
        ring
      rw [he]

/-- Directional finite-difference vanishing supplies all the line polynomials
needed for the lattice degree model, with the same uniform degree bound. -/
theorem polynomial_on_lines {σ : Type*} (d : ℕ) (f : (σ → ℤ) → ℚ)
    (h : ∀ y : σ → ℤ, (fwdDiff y)^[d+1] f = 0) :
    ∀ x y : σ → ℤ, ∃ p : Polynomial ℚ, p.natDegree ≤ d ∧
      ∀ t : ℤ, f (fun i => x i + t * y i) = p.eval (t : ℚ) := by
  intro x y
  apply exists_polynomial d
  funext t
  rw [iterate_on_line, h y]
  rfl

end IntegerDifferencePolynomial
end

end


section

set_option autoImplicit false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity

theorem line_degree_model_of_finite_differences
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val))
    (hgeometry : ∃ (m : ℕ)
      (α : Multiplicative G.Point →* ((Fin m → ℤ) ≃ₗ[ℤ] (Fin m → ℤ)))
      (c : G.FactorIndex → (Fin m → ℤ)),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
        ∃ f : (Fin m → ℤ) → ℚ,
          (∀ y : Fin m → ℤ,
            (fwdDiff y)^[SectionThree.locusDimension G.ambient (Subtype.val '' V) + 1] f = 0) ∧
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              f (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i))) :
    ∃ (m : ℕ)
      (α : Multiplicative G.Point →* ((Fin m → ℤ) ≃ₗ[ℤ] (Fin m → ℤ)))
      (c : G.FactorIndex → (Fin m → ℤ)),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
        ∃ f : (Fin m → ℤ) → ℚ,
          (∀ x y : Fin m → ℤ, ∃ q : Polynomial ℚ,
            q.natDegree ≤ SectionThree.locusDimension G.ambient (Subtype.val '' V) ∧
            ∀ t : ℤ, f (fun j => x j + t * y j) = q.eval (t : ℚ)) ∧
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              f (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i)) := by
  obtain ⟨m, α, c, h⟩ := hgeometry
  refine ⟨m, α, c, ?_⟩
  intro V hV
  obtain ⟨f, hdiff, hdegree⟩ := h V hV
  refine ⟨f, ?_, hdegree⟩
  exact IntegerDifferencePolynomial.polynomial_on_lines
    (SectionThree.locusDimension G.ambient (Subtype.val '' V)) f hdiff

end PhilipponMultiplicity
end

end

set_option autoImplicit false
open PhilipponMultiplicity
open scoped BigOperators Topology

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val)) :
    ∃ (m : ℕ)
      (α : Multiplicative G.Point →* ((Fin m → ℤ) ≃ₗ[ℤ] (Fin m → ℤ)))
      (c : G.FactorIndex → (Fin m → ℤ)),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
        ∃ f : (Fin m → ℤ) → ℚ,
          (∀ x y : Fin m → ℤ, ∃ q : Polynomial ℚ,
            q.natDegree ≤ SectionThree.locusDimension G.ambient (Subtype.val '' V) ∧
            ∀ t : ℤ, f (fun j => x j + t * y j) = q.eval (t : ℚ)) ∧
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              f (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i)) := by
  exact line_degree_model_of_finite_differences K hK G τ hzero hadd hregular
    (closure_action_has_finite_difference_degree_model K hK G τ hzero hadd hregular)
