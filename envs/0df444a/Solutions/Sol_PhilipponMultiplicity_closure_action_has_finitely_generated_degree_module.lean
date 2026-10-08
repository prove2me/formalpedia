-- Prove2me | solution 1 for PhilipponMultiplicity.closure_action_has_finitely_generated_degree_module
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-05T10:36:50.288478+00:00
-- url     : https://prove2.me/submissions/0d06ca98-b1c4-4867-9230-76f388f145a2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_closure_action_has_multilinear_degree_model
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_Support
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

set_option autoImplicit false

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace PhilipponMultiplicity.IntersectionAction

variable {R A B : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

/-- Linear maps preserve the annihilating scalar of a torsion element. -/
theorem map_mem_torsion (f : A →ₗ[R] B) {x : A}
    (hx : x ∈ Submodule.torsion R A) : f x ∈ Submodule.torsion R B := by
  obtain ⟨r, hr⟩ := hx
  refine ⟨r, ?_⟩
  change (r : R) • x = 0 at hr
  change (r : R) • f x = 0
  rw [← f.map_smul, hr, f.map_zero]

theorem equiv_mem_torsion_iff (e : B ≃ₗ[R] A) (x : B) :
    e x ∈ Submodule.torsion R A ↔ x ∈ Submodule.torsion R B := by
  constructor
  · intro hx
    simpa using map_mem_torsion e.symm.toLinearMap hx
  · exact map_mem_torsion e.toLinearMap

/-- Transport a representation along a module equivalence. -/
def conjugateAction {Γ : Type*} [Group Γ]
    (e : B ≃ₗ[R] A) (ρ : Γ →* (A ≃ₗ[R] A)) : Γ →* (B ≃ₗ[R] B) where
  toFun g := (e.trans (ρ g)).trans e.symm
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

@[simp]
theorem conjugateAction_apply {Γ : Type*} [Group Γ]
    (e : B ≃ₗ[R] A) (ρ : Γ →* (A ≃ₗ[R] A)) (g : Γ) (x : B) :
    conjugateAction e ρ g x = e.symm (ρ g (e x)) := rfl

/-- The condition of acting trivially modulo torsion is independent of presentation. -/
theorem conjugateAction_torsion_iff {Γ : Type*} [Group Γ]
    (e : B ≃ₗ[R] A) (ρ : Γ →* (A ≃ₗ[R] A)) (g : Γ) :
    (∀ x, conjugateAction e ρ g x - x ∈ Submodule.torsion R B) ↔
      ∀ x, ρ g x - x ∈ Submodule.torsion R A := by
  constructor
  · intro h x
    have hx := map_mem_torsion e.toLinearMap (h (e.symm x))
    simpa using hx
  · intro h x
    have hx := map_mem_torsion e.symm.toLinearMap (h (e x))
    simpa using hx

/-- The inverse also acts trivially modulo torsion. -/
theorem inverse_displacement_mem_torsion {Γ : Type*} [Group Γ]
    (ρ : Γ →* (A ≃ₗ[R] A)) (g : Γ)
    (h : ∀ x, ρ g x - x ∈ Submodule.torsion R A) (x : A) :
    ρ g⁻¹ x - x ∈ Submodule.torsion R A := by
  have hx := (Submodule.torsion R A).neg_mem (h (ρ g⁻¹ x))
  simpa using hx

/-- Multilinear maps to a torsion-free module depend only on their arguments
modulo torsion. The product of the coordinate annihilators cancels, including
the empty product when there are no arguments. -/
theorem multilinear_eq_of_torsion [IsDomain R] [Module.IsTorsionFree R B]
    {ι : Type*} [Fintype ι] (f : MultilinearMap R (fun _ : ι => A) B)
    (x y : ι → A) (h : ∀ i, x i - y i ∈ Submodule.torsion R A) : f x = f y := by
  classical
  choose r hr using h
  have hxy : (fun i => (r i : R) • x i) = fun i => (r i : R) • y i := by
    funext i
    apply sub_eq_zero.mp
    rw [← smul_sub]
    exact hr i
  have hf := congrArg f hxy
  rw [f.map_smul_univ, f.map_smul_univ] at hf
  have hn : (∏ i, (r i : R)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => nonZeroDivisors.coe_ne_zero (r i)
  apply sub_eq_zero.mp
  have hz : (∏ i, (r i : R)) • (f x - f y) = 0 := by
    rw [smul_sub, hf, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left hn

/-- A finite module action has a finite free quotient presentation with exactly
the same elements acting trivially modulo torsion. -/
theorem exists_presented_action [Module.Finite R A] {Γ : Type*} [Group Γ]
    (ρ : Γ →* (A ≃ₗ[R] A)) :
    ∃ (m : ℕ) (L : Submodule R (Fin m → R))
      (α : Γ →* (((Fin m → R) ⧸ L) ≃ₗ[R] ((Fin m → R) ⧸ L))),
      ∀ g, (∀ x, α g x - x ∈ Submodule.torsion R ((Fin m → R) ⧸ L)) ↔
        ∀ x, ρ g x - x ∈ Submodule.torsion R A := by
  obtain ⟨m, L, ⟨e⟩⟩ := Module.Finite.exists_fin_quot_equiv R A
  exact ⟨m, L, conjugateAction e ρ, conjugateAction_torsion_iff e ρ⟩

end PhilipponMultiplicity.IntersectionAction
end

end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity

theorem degree_module_of_multilinear_model
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val))
    (hmodel : ∃ (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A)
      (_ : Module.Finite ℤ A) (α : Multiplicative G.Point →* (A ≃ₗ[ℤ] A))
      (c : G.FactorIndex → A),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
        ∃ I : MultilinearMap ℤ
          (fun _ : Fin (SectionThree.locusDimension G.ambient (Subtype.val '' V)) => A) ℚ,
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              I (fun _ => α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i))) :
    ∃ (m : ℕ) (L : Submodule ℤ (Fin m → ℤ))
      (α : Multiplicative G.Point →*
        (((Fin m → ℤ) ⧸ L) ≃ₗ[ℤ] ((Fin m → ℤ) ⧸ L))),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
      ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
        (∀ x, α (Multiplicative.ofAdd g) x - x ∈
          Submodule.torsion ℤ ((Fin m → ℤ) ⧸ L)) →
        SectionThree.locusDegreeValue G.ambient (Subtype.val '' V) D =
      SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D := by
  classical
  obtain ⟨A, hA, hmodule, hfinite, α, c, hmodel⟩ := hmodel
  obtain ⟨m, L, β, hβ⟩ := IntersectionAction.exists_presented_action α
  refine ⟨m, L, β, ?_⟩
  intro V hV g D hD hg
  obtain ⟨I, hI⟩ := hmodel V hV
  have hα := (hβ (Multiplicative.ofAdd g)).mp hg
  have hinv (x : A) : α (Multiplicative.ofAdd (-g)) x - x ∈
      Submodule.torsion ℤ A := by
    simpa using IntersectionAction.inverse_displacement_mem_torsion α
      (Multiplicative.ofAdd g) hα x
  have hsame : I (fun _ => α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i)) =
      I (fun _ => ∑ i, (D i : ℤ) • c i) :=
    IntersectionAction.multilinear_eq_of_torsion I _ _ (fun _ => hinv _)
  have h0 := hI 0 D hD
  have hzero_image : τ (0 : G.Point) '' V = V := by rw [hzero]; simp
  have hbase : SectionThree.locusDegreeValue G.ambient (Subtype.val '' V) D =
      I (fun _ => ∑ i, (D i : ℤ) • c i) := by
    simpa [hzero_image] using h0
  exact hbase.trans (hsame.symm.trans (hI g D hD).symm)

end PhilipponMultiplicity

end

end

set_option maxHeartbeats 1000000
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
    ∃ (m : ℕ) (L : Submodule ℤ (Fin m → ℤ))
      (α : Multiplicative G.Point →*
        (((Fin m → ℤ) ⧸ L) ≃ₗ[ℤ] ((Fin m → ℤ) ⧸ L))),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
      ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
        (∀ x, α (Multiplicative.ofAdd g) x - x ∈
          Submodule.torsion ℤ ((Fin m → ℤ) ⧸ L)) →
        SectionThree.locusDegreeValue G.ambient (Subtype.val '' V) D =
      SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D := by
  exact degree_module_of_multilinear_model K hK G τ hzero hadd hregular
    (closure_action_has_multilinear_degree_model K hK G τ hzero hadd hregular)
