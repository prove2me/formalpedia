-- Prove2me | solution 1 for VaryingConstants.buckingham_pi
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-03T14:48:05.229221+00:00
-- url     : https://prove2.me/submissions/54c7961d-8ba7-4a4e-97e1-43df86fb7841

import Theorems.Thm_VaryingConstants_finrank_dimensionlessExponents
import Theorems.Thm_VaryingConstants_only_dimensionless_variations_measurable

open VaryingConstants Module

private lemma monomial_exp_log {n : ℕ} (a x : Fin n → ℝ) (hx : IsPositive x) :
    powerMonomial a x = Real.exp (∑ i, a i * Real.log (x i)) := by
  unfold powerMonomial
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Real.rpow_def_of_pos (hx i), mul_comm]

/-- Equality of the basis monomials determines every monomial from the subspace. -/
private lemma basis_monomials_determine_all {n k : ℕ}
    (Z : Submodule ℝ (Fin n → ℝ)) (b : Basis (Fin k) ℝ Z)
    (x y : Fin n → ℝ) (hx : IsPositive x) (hy : IsPositive y)
    (hxy : ∀ l, powerMonomial (b l) x = powerMonomial (b l) y) :
    ∀ a ∈ Z, powerMonomial a x = powerMonomial a y := by
  let L : Z →ₗ[ℝ] ℝ :=
    { toFun := fun a => ∑ i, (a : Fin n → ℝ) i * (Real.log (x i) - Real.log (y i))
      map_add' := by
        intro a c
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r a
        simp [smul_eq_mul, Finset.mul_sum, mul_assoc] }
  have hL : L = 0 := by
    apply b.ext
    intro l
    have h := hxy l
    rw [monomial_exp_log _ x hx, monomial_exp_log _ y hy] at h
    have hlogs := Real.exp_injective h
    change (∑ i, (b l : Fin n → ℝ) i * (Real.log (x i) - Real.log (y i))) = 0
    simpa only [mul_sub, Finset.sum_sub_distrib, sub_eq_zero] using hlogs
  intro a ha
  have hzero := LinearMap.congr_fun hL (⟨a, ha⟩ : Z)
  change (∑ i, a i * (Real.log (x i) - Real.log (y i))) = 0 at hzero
  rw [monomial_exp_log a x hx, monomial_exp_log a y hy]
  congr 1
  simpa only [mul_sub, Finset.sum_sub_distrib, sub_eq_zero] using hzero

/-- Buckingham's dimensionless coordinates factor every unit-invariant observable. -/
theorem solution {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ) :
    ∃ a : Fin (n - D.rank) → (Fin n → ℝ),
      (∀ l, a l ∈ dimensionlessExponents D) ∧ LinearIndependent ℝ a ∧
      ∀ f : (Fin n → ℝ) → ℝ, IsUnitInvariant D f →
        ∃ F : (Fin (n - D.rank) → ℝ) → ℝ,
          ∀ x : Fin n → ℝ, IsPositive x → f x = F (fun l => powerMonomial (a l) x) := by
  classical
  let Z := dimensionlessExponents D
  let b : Basis (Fin (n - D.rank)) ℝ Z :=
    Module.finBasisOfFinrankEq ℝ Z (finrank_dimensionlessExponents D)
  let a : Fin (n - D.rank) → (Fin n → ℝ) := fun l => b l
  refine ⟨a, fun l => (b l).property, ?_, ?_⟩
  · exact b.linearIndependent.map' Z.subtype (Submodule.ker_subtype Z)
  · intro f hf
    let P := {x : Fin n → ℝ // IsPositive x}
    let π : P → (Fin (n - D.rank) → ℝ) := fun x l => powerMonomial (a l) x
    have hfactor : Function.FactorsThrough (fun x : P => f x) π := by
      intro x y hxy
      apply only_dimensionless_variations_measurable D f hf x y x.property y.property
      apply basis_monomials_determine_all Z b x y x.property y.property
      intro l
      exact congrFun hxy l
    obtain ⟨F, hF⟩ := (Function.factorsThrough_iff (fun x : P => f x)).mp hfactor
    refine ⟨F, ?_⟩
    intro x hx
    exact congrFun hF (⟨x, hx⟩ : P)
