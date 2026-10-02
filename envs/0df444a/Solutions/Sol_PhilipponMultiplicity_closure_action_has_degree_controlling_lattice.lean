-- Prove2me | solution 1 for PhilipponMultiplicity.closure_action_has_degree_controlling_lattice
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-02T09:10:11.808909+00:00
-- url     : https://prove2.me/submissions/72f8d24d-6306-4a72-92b5-3478dc9d3981
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_closure_action_has_finitely_generated_degree_module
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_Support
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.TorsionLattice

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]

/-- A linear map preserves torsion, with the same annihilating scalar. -/
theorem map_mem_torsion (f : A →ₗ[R] A) {x : A}
    (hx : x ∈ Submodule.torsion R A) : f x ∈ Submodule.torsion R A := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  change (n : R) • x = 0 at hn
  change (n : R) • f x = 0
  rw [← f.map_smul, hn, f.map_zero]

/-- Torsion is invariant under every automorphism, even when it is nontrivial. -/
theorem map_torsion_eq (f : A ≃ₗ[R] A) :
    (Submodule.torsion R A).map f.toLinearMap = Submodule.torsion R A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact map_mem_torsion f.toLinearMap hy
  · intro hx
    exact ⟨f.symm x, map_mem_torsion f.symm.toLinearMap hx, f.apply_symm_apply x⟩

/-- The action on the quotient by torsion, constructed functorially. -/
def quotientAction {Γ : Type*} [Group Γ] (ρ : Γ →* (A ≃ₗ[R] A)) :
    Γ →* ((A ⧸ Submodule.torsion R A) ≃ₗ[R] (A ⧸ Submodule.torsion R A)) where
  toFun g := Submodule.Quotient.equiv _ _ (ρ g) (map_torsion_eq (ρ g))
  map_one' := by
    ext q
    obtain ⟨x, rfl⟩ := (Submodule.torsion R A).mkQ_surjective q
    simp
  map_mul' g h := by
    ext q
    obtain ⟨x, rfl⟩ := (Submodule.torsion R A).mkQ_surjective q
    simp

@[simp]
theorem quotientAction_mk {Γ : Type*} [Group Γ] (ρ : Γ →* (A ≃ₗ[R] A))
    (g : Γ) (x : A) :
    quotientAction ρ g ((Submodule.torsion R A).mkQ x) =
      (Submodule.torsion R A).mkQ (ρ g x) := by
  rfl

/-- The quotient action is trivial exactly when every displacement is torsion. -/
theorem quotientAction_eq_one_iff {Γ : Type*} [Group Γ]
    (ρ : Γ →* (A ≃ₗ[R] A)) (g : Γ) :
    quotientAction ρ g = 1 ↔ ∀ x, ρ g x - x ∈ Submodule.torsion R A := by
  constructor
  · intro h x
    have hx := congrArg (fun f : (A ⧸ Submodule.torsion R A) ≃ₗ[R]
      (A ⧸ Submodule.torsion R A) => f ((Submodule.torsion R A).mkQ x)) h
    change (Submodule.torsion R A).mkQ (ρ g x) =
      (Submodule.torsion R A).mkQ x at hx
    exact (Submodule.Quotient.eq _).mp hx
  · intro h
    ext q
    obtain ⟨x, rfl⟩ := (Submodule.torsion R A).mkQ_surjective q
    change (Submodule.torsion R A).mkQ (ρ g x) = (Submodule.torsion R A).mkQ x
    exact (Submodule.Quotient.eq _).mpr (h x)

/-- A finitely generated module action over a PID has a finite matrix
representation whose kernel is exactly the action trivial modulo torsion.
No freeness assumption on the original module and no positive rank are needed. -/
theorem exists_matrix_action [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R A]
    {Γ : Type*} [Group Γ]
    (ρ : Γ →* (A ≃ₗ[R] A)) :
    ∃ (r : ℕ) (σ : Γ →* Matrix.GeneralLinearGroup (Fin r) R),
      ∀ g, σ g = 1 ↔ ∀ x, ρ g x - x ∈ Submodule.torsion R A := by
  let Q := A ⧸ Submodule.torsion R A
  let : Module.IsTorsionFree R Q := Submodule.QuotientTorsion.instIsTorsionFree
  let : Module.Free R Q := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis R Q
  let e : Matrix.GeneralLinearGroup (Fin (Module.finrank R Q)) R ≃* (Q ≃ₗ[R] Q) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv R Q)
  let σ := e.symm.toMonoidHom.comp (quotientAction ρ)
  refine ⟨Module.finrank R Q, σ, ?_⟩
  intro g
  have he : σ g = 1 ↔ quotientAction ρ g = 1 := by
    change e.symm (quotientAction ρ g) = 1 ↔ _
    rw [← e.symm.map_one, e.symm.injective.eq_iff]
  exact he.trans (quotientAction_eq_one_iff ρ g)

end PhilipponMultiplicity.TorsionLattice
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem closure_lattice_of_finitely_generated_degree_module
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val))
    (hinput : ∃ (m : ℕ) (L : Submodule ℤ (Fin m → ℤ))
      (α : Multiplicative G.Point →*
        (((Fin m → ℤ) ⧸ L) ≃ₗ[ℤ] ((Fin m → ℤ) ⧸ L))),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
      ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
        (∀ x, α (Multiplicative.ofAdd g) x - x ∈
          Submodule.torsion ℤ ((Fin m → ℤ) ⧸ L)) →
        SectionThree.locusDegreeValue G.ambient (Subtype.val '' V) D =
      SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D) :
    ∃ (r : ℕ) (ρ : Multiplicative G.Point →*
        Matrix.GeneralLinearGroup (Fin r) ℤ),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
      ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
        ρ (Multiplicative.ofAdd g) = 1 →
        SectionThree.locusDegreeValue G.ambient (Subtype.val '' V) D =
      SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D := by
  obtain ⟨m, L, α, hdegree⟩ := hinput
  obtain ⟨r, ρ, hρ⟩ := TorsionLattice.exists_matrix_action α
  refine ⟨r, ρ, ?_⟩
  intro V hV g D hD hg
  exact hdegree V hV g D hD ((hρ (Multiplicative.ofAdd g)).mp hg)

end PhilipponMultiplicity
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val)) :
    ∃ (r : ℕ) (ρ : Multiplicative G.Point →*
        Matrix.GeneralLinearGroup (Fin r) ℤ),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
      ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
        ρ (Multiplicative.ofAdd g) = 1 →
        SectionThree.locusDegreeValue G.ambient (Subtype.val '' V) D =
      SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D := by
  exact closure_lattice_of_finitely_generated_degree_module K hK G τ hzero hadd hregular
    (closure_action_has_finitely_generated_degree_module K hK G τ hzero hadd hregular)
