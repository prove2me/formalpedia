-- Prove2me | solution 1 for PhilipponMultiplicity.closure_action_has_finite_difference_degree_model
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-07T11:40:01.7768+00:00
-- url     : https://prove2.me/submissions/0458a551-9bb2-496d-88d2-7e9fb80de621
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_closure_action_has_finitely_generated_difference_degree_model
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_Support
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.RingTheory.Finiteness.Cardinality


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
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.TorsionDifference

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- A function with zero first difference is constant along the corresponding orbit. -/
theorem invariant_nsmul (f : A → ℚ) (y : A) (h : fwdDiff y f = 0)
    (x : A) (n : ℕ) : f (x + n • y) = f x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := congrFun h (x + n • y)
      change f (x + n • y + y) - f (x + n • y) = 0 at hs
      simpa only [add_nsmul, one_nsmul, ← add_assoc] using
        (sub_eq_zero.mp hs).trans ih

/-- If the second difference vanishes, the values on a ray form an arithmetic progression. -/
theorem affine_nsmul (f : A → ℚ) (y : A) (h : fwdDiff y (fwdDiff y f) = 0)
    (x : A) (n : ℕ) : f (x + n • y) = f x + n • (fwdDiff y f x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := invariant_nsmul (fwdDiff y f) y h x n
      change f (x + n • y + y) - f (x + n • y) = fwdDiff y f x at hs
      rw [sub_eq_iff_eq_add, ih] at hs
      simpa only [add_nsmul, one_nsmul, ← add_assoc, add_comm, add_left_comm] using hs

/-- A nilpotent difference in a finite-order direction is already zero.
Induction lowers the nilpotence order; the last affine increment vanishes
because its nonzero period is invertible in the rational codomain. -/
theorem finite_order_difference_eq_zero (f : A → ℚ) (y : A)
    (n : ℕ) (hn : n ≠ 0) (hy : n • y = 0) (d : ℕ)
    (hd : (fwdDiff y)^[d+1] f = 0) : fwdDiff y f = 0 := by
  induction d generalizing f with
  | zero => simpa using hd
  | succ d ih =>
      have hsecond : fwdDiff y (fwdDiff y f) = 0 :=
        ih (fwdDiff y f) (by simpa only [Function.iterate_succ_apply] using hd)
      funext x
      have hs := affine_nsmul f y hsecond x n
      rw [hy, add_zero] at hs
      have hz : (n : ℚ) * fwdDiff y f x = 0 := by
        have := (add_eq_left.mp hs.symm)
        simpa only [nsmul_eq_mul] using this
      exact (mul_eq_zero.mp hz).resolve_left (Nat.cast_ne_zero.mpr hn)

/-- Rational functions with a vanishing high difference ignore torsion in that direction. -/
theorem eq_add_torsion [Module ℤ A] (f : A → ℚ) (d : ℕ)
    (h : ∀ y, (fwdDiff y)^[d+1] f = 0)
    (x y : A) (hy : y ∈ Submodule.torsion ℤ A) : f (x+y) = f x := by
  obtain ⟨n, hn⟩ := hy
  have hn' : (n : ℤ) • y = 0 := by
    exact (int_smul_eq_zsmul ‹Module ℤ A› (n : ℤ) y).symm.trans hn
  have hdiff := finite_order_difference_eq_zero f y (n : ℤ).natAbs
    (Int.natAbs_ne_zero.mpr (nonZeroDivisors.coe_ne_zero n))
    (natAbs_nsmul_eq_zero.mpr hn') d (h y)
  exact sub_eq_zero.mp (congrFun hdiff x)

/-- Iterated differences commute with pullback by additive maps. -/
theorem iterate_comp (q : A →+ B) (f : B → ℚ) (y : A) (n : ℕ) (x : A) :
    (fwdDiff y)^[n] (f ∘ q) x = (fwdDiff (q y))^[n] f (q x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply', fwdDiff]
      rw [ih, ih, q.map_add]

/-- Descent to the torsion-free quotient preserves every directional degree bound. -/
theorem exists_quotient_function [Module ℤ A] (f : A → ℚ) (d : ℕ)
    (h : ∀ y, (fwdDiff y)^[d+1] f = 0) :
    ∃ F : (A ⧸ Submodule.torsion ℤ A) → ℚ,
      (∀ x, F ((Submodule.torsion ℤ A).mkQ x) = f x) ∧
      ∀ y, (fwdDiff y)^[d+1] F = 0 := by
  let T := Submodule.torsion ℤ A
  let q := T.mkQ
  let s := Function.surjInv T.mkQ_surjective
  let F := f ∘ s
  have hF (x : A) : F (q x) = f x := by
    have he : q (s (q x)) = q x := Function.surjInv_eq T.mkQ_surjective (q x)
    have ht : s (q x) - x ∈ T := (Submodule.Quotient.eq T).mp he
    have hx := eq_add_torsion f d h x (s (q x) - x) ht
    simpa only [← add_sub_assoc, add_sub_cancel_left, F, Function.comp_apply] using hx
  refine ⟨F, hF, ?_⟩
  intro y
  obtain ⟨a, rfl⟩ := T.mkQ_surjective y
  funext z
  obtain ⟨x, rfl⟩ := T.mkQ_surjective z
  have heq : F ∘ q.toAddMonoidHom = f := funext hF
  have hh := iterate_comp q.toAddMonoidHom F a (d+1) x
  rw [heq, h a] at hh
  exact hh.symm

/-- A finitely generated abelian group action has a surjection onto a finite
integer lattice with torsion kernel, intertwining the original and quotient actions. -/
theorem exists_lattice_projection [Module ℤ A] [Module.Finite ℤ A]
    {Γ : Type*} [Group Γ] (ρ : Γ →* (A ≃ₗ[ℤ] A)) :
    ∃ (m : ℕ) (q : A →ₗ[ℤ] (Fin m → ℤ))
      (α : Γ →* ((Fin m → ℤ) ≃ₗ[ℤ] (Fin m → ℤ))),
      Function.Surjective q ∧
      (∀ x y, q x = q y ↔ x-y ∈ Submodule.torsion ℤ A) ∧
      ∀ g x, q (ρ g x) = α g (q x) := by
  let Q := A ⧸ Submodule.torsion ℤ A
  let : Module ℤ Q := Submodule.Quotient.module _
  let : Module.IsTorsionFree ℤ Q := Submodule.QuotientTorsion.instIsTorsionFree
  let : Module.Free ℤ Q := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ Q
  let e := b.equivFun
  let q := e.toLinearMap.comp (Submodule.torsion ℤ A).mkQ
  let α := IntersectionAction.conjugateAction e.symm (TorsionLattice.quotientAction ρ)
  refine ⟨Module.finrank ℤ Q, q, α,
    e.surjective.comp (Submodule.torsion ℤ A).mkQ_surjective, ?_, ?_⟩
  · intro x y
    exact e.injective.eq_iff.trans (Submodule.Quotient.eq _)
  · intro g x
    simp [q, α]
    rfl

/-- The same lattice and action serve any family of functions; no choices of
bases or projections depend on the function or its degree. -/
theorem exists_function_on_lattice [Module ℤ A] {m : ℕ}
    (q : A →ₗ[ℤ] (Fin m → ℤ)) (hq : Function.Surjective q)
    (hker : ∀ x y, q x = q y ↔ x-y ∈ Submodule.torsion ℤ A)
    (f : A → ℚ) (d : ℕ) (h : ∀ y, (fwdDiff y)^[d+1] f = 0) :
    ∃ F : (Fin m → ℤ) → ℚ,
      (∀ y, (fwdDiff y)^[d+1] F = 0) ∧ ∀ x, F (q x) = f x := by
  let s := Function.surjInv hq
  let F := f ∘ s
  have hF (x : A) : F (q x) = f x := by
    have ht := (hker (s (q x)) x).mp (Function.surjInv_eq hq (q x))
    simpa only [F, Function.comp_apply, ← add_sub_assoc, add_sub_cancel_left] using
      eq_add_torsion f d h x (s (q x)-x) ht
  refine ⟨F, ?_, hF⟩
  intro y
  obtain ⟨a, rfl⟩ := hq y
  funext z
  obtain ⟨x, rfl⟩ := hq z
  have heq : F ∘ q.toAddMonoidHom = f := funext hF
  have hh := iterate_comp q.toAddMonoidHom F a (d+1) x
  rw [heq, h a] at hh
  exact hh.symm

end PhilipponMultiplicity.TorsionDifference
end

end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity

theorem lattice_degree_model_of_finitely_generated_differences
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val))
    (hgeometry : ∃ (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A)
      (_ : Module.Finite ℤ A)
      (α : Multiplicative G.Point →* (A ≃ₗ[ℤ] A))
      (c : G.FactorIndex → A),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
        ∃ f : A → ℚ,
          (∀ y : A,
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
          (∀ y : Fin m → ℤ,
            (fwdDiff y)^[SectionThree.locusDimension G.ambient (Subtype.val '' V) + 1] f = 0) ∧
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              f (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i)) := by
  obtain ⟨A, hA, hmodule, hfinite, α, c, hgeometry⟩ := hgeometry
  obtain ⟨m, q, β, hq, hker, haction⟩ := TorsionDifference.exists_lattice_projection α
  refine ⟨m, β, fun i => q (c i), ?_⟩
  intro V hV
  obtain ⟨f, hdiff, hdegree⟩ := hgeometry V hV
  obtain ⟨F, hFdiff, hFq⟩ := TorsionDifference.exists_function_on_lattice
    q hq hker f (SectionThree.locusDimension G.ambient (Subtype.val '' V)) hdiff
  refine ⟨F, hFdiff, ?_⟩
  intro g D hD
  calc
    SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
        f (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i)) := hdegree g D hD
    _ = F (q (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i))) := (hFq _).symm
    _ = F (β (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • q (c i))) := by
      rw [haction]
      simp

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
          (∀ y : Fin m → ℤ,
            (fwdDiff y)^[SectionThree.locusDimension G.ambient (Subtype.val '' V) + 1] f = 0) ∧
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              f (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i)) := by
  exact lattice_degree_model_of_finitely_generated_differences K hK G τ hzero hadd hregular
    (closure_action_has_finitely_generated_difference_degree_model K hK G τ hzero hadd hregular)
