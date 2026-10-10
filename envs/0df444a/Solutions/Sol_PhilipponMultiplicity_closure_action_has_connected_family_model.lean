-- Prove2me | solution 1 for PhilipponMultiplicity.closure_action_has_connected_family_model
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-10T00:22:53.474624+00:00
-- url     : https://prove2.me/submissions/6b484ad3-d4a9-408f-9079-3b583558309a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_closure_action_has_local_complex_model
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_Support
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Topology.LocallyConstant.Basic


section

set_option autoImplicit false
open scoped BigOperators
open CategoryTheory
noncomputable section

namespace PhilipponMultiplicity.ComplexEuler

universe u
variable {K : Type u} [Field K]

theorem short_homology_finite (S : ShortComplex (ModuleCat.{u} K))
    [Module.Finite K S.X₂] : Module.Finite K S.homology := by
  let : Module.Finite K S.moduleCatLeftHomologyData.H :=
    show Module.Finite K (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
      from inferInstance
  exact Module.Finite.equiv S.moduleCatHomologyIso.symm.toLinearEquiv

/-- Rank-nullity computes homology without assuming constant differential ranks. -/
theorem short_complex_rank (S : ShortComplex (ModuleCat.{u} K))
    [Module.Finite K S.X₁] [Module.Finite K S.X₂] :
    Module.finrank K S.homology + Module.finrank K (LinearMap.range S.f.hom) +
      Module.finrank K (LinearMap.range S.g.hom) = Module.finrank K S.X₂ := by
  have hf := S.f.hom.finrank_range_add_finrank_ker
  have hc := S.moduleCatToCycles.finrank_range_add_finrank_ker
  have hker : LinearMap.ker S.moduleCatToCycles = LinearMap.ker S.f.hom :=
    LinearMap.ker_codRestrict _ _ _
  rw [hker] at hc
  have hquot := (LinearMap.range S.moduleCatToCycles).finrank_quotient_add_finrank
  have hhom := S.moduleCatHomologyIso.toLinearEquiv.finrank_eq
  change Module.finrank K S.homology =
    Module.finrank K (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) at hhom
  have hg := S.g.hom.finrank_range_add_finrank_ker
  omega

theorem cochain_rank (V : CochainComplex (ModuleCat.{u} K) ℤ)
    [∀ i, Module.Finite K (V.X i)] (i : ℤ) :
    Module.finrank K (V.homology i) +
      Module.finrank K (LinearMap.range (V.d (i-1) i).hom) +
      Module.finrank K (LinearMap.range (V.d i (i+1)).hom) =
      Module.finrank K (V.X i) := by
  have hp : (ComplexShape.up ℤ).prev i = i-1 :=
    (ComplexShape.up ℤ).prev_eq' (by change i-1+1=i; omega)
  have hn : (ComplexShape.up ℤ).next i = i+1 :=
    (ComplexShape.up ℤ).next_eq' rfl
  let : Module.Finite K (V.sc i).X₁ :=
    show Module.Finite K (V.X ((ComplexShape.up ℤ).prev i)) from inferInstance
  let : Module.Finite K (V.sc i).X₂ :=
    show Module.Finite K (V.X i) from inferInstance
  have h := short_complex_rank (V.sc i)
  change Module.finrank K (V.homology i) +
    Module.finrank K (LinearMap.range (V.d ((ComplexShape.up ℤ).prev i) i).hom) +
    Module.finrank K (LinearMap.range (V.d i ((ComplexShape.up ℤ).next i)).hom) =
      Module.finrank K (V.X i) at h
  rw [congrArg (fun j => Module.finrank K (LinearMap.range (V.d j i).hom)) hp,
    congrArg (fun j => Module.finrank K (LinearMap.range (V.d i j).hom)) hn] at h
  exact h

def sign (i : ℤ) : ℤ := Int.negOnePow i

theorem sign_succ (i : ℤ) : sign (i+1) = -sign i := by
  simp [sign, Int.negOnePow_succ]

theorem signed_finite (r : ℤ → ℕ) (hr : Function.HasFiniteSupport r) :
    Function.HasFiniteSupport (fun i => sign i * (r i : ℤ)) := by
  apply hr.subset
  intro i hi
  change r i ≠ 0
  intro h
  exact hi (by simp [h])

theorem alternating_shift (b : ℤ → ℤ) :
    (∑ᶠ i : ℤ, sign i * b (i-1)) = -(∑ᶠ i : ℤ, sign i * b i) := by
  have h := finsum_comp_equiv (Equiv.addRight (1 : ℤ))
    (f := fun i : ℤ => sign i * b (i-1))
  change (∑ᶠ i : ℤ, sign (i+1) * b (i+1-1)) = _ at h
  simp only [add_sub_cancel_right] at h
  rw [← h]
  simp only [sign_succ, neg_mul, finsum_neg_distrib]

/-- The ranks of boundaries cancel, including the end terms of the finite complex. -/
theorem alternating_rank_identity (r h b : ℤ → ℕ)
    (hr : Function.HasFiniteSupport r)
    (heq : ∀ i, h i + b (i-1) + b i = r i) :
    (∑ᶠ i, sign i * (h i : ℤ)) = ∑ᶠ i, sign i * (r i : ℤ) := by
  have hh : Function.HasFiniteSupport h := hr.subset (by
    intro i hi
    change h i ≠ 0 at hi
    change r i ≠ 0
    have := heq i
    omega)
  have hb : Function.HasFiniteSupport b := hr.subset (by
    intro i hi
    change b i ≠ 0 at hi
    change r i ≠ 0
    have := heq i
    omega)
  have hbp : Function.HasFiniteSupport (fun i => b (i-1)) :=
    hb.fun_comp_of_injective (fun _ _ h => by omega)
  have hsum : (∑ᶠ i, sign i * (r i : ℤ)) =
      (∑ᶠ i, sign i * (h i : ℤ)) + (∑ᶠ i, sign i * (b (i-1) : ℤ)) +
        (∑ᶠ i, sign i * (b i : ℤ)) := by
    calc
      _ = ∑ᶠ i, ((sign i * (h i : ℤ) + sign i * (b (i-1) : ℤ)) +
          sign i * (b i : ℤ)) := by
        apply finsum_congr
        intro i
        rw [← heq i, Nat.cast_add, Nat.cast_add]
        ring
      _ = _ := by
        have h₁ := finsum_add_distrib ((signed_finite h hh).add (signed_finite _ hbp))
          (signed_finite b hb)
        have h₂ := finsum_add_distrib (signed_finite h hh) (signed_finite _ hbp)
        simpa only [Pi.add_apply] using
          h₁.trans (congrArg (fun x => x + ∑ᶠ i, sign i * (b i : ℤ)) h₂)
  rw [alternating_shift (fun i => (b i : ℤ))] at hsum
  omega

theorem homology_euler_eq (V : CochainComplex (ModuleCat.{u} K) ℤ)
    [∀ i, Module.Finite K (V.X i)]
    (hfinite : Function.HasFiniteSupport (fun i => Module.finrank K (V.X i))) :
    V.homologyEulerChar = V.eulerChar := by
  apply alternating_rank_identity _ _
    (fun i => Module.finrank K (LinearMap.range (V.d i (i+1)).hom)) hfinite
  intro i
  rw [congrArg (fun j => Module.finrank K (LinearMap.range (V.d (i-1) j).hom))
    (sub_add_cancel i 1)]
  exact cochain_rank V i

/-- A bounded complex with a fixed rank vector has the corresponding Euler value. -/
theorem homology_euler_of_ranks (V : CochainComplex (ModuleCat.{u} K) ℤ)
    [∀ i, Module.Finite K (V.X i)] (r : ℤ → ℕ) (hr : Function.HasFiniteSupport r)
    (hrank : ∀ i, Module.finrank K (V.X i) = r i) :
    V.homologyEulerChar = ∑ᶠ i, sign i * (r i : ℤ) := by
  have hfinite : Function.HasFiniteSupport (fun i => Module.finrank K (V.X i)) := by
    simpa only [hrank] using hr
  rw [homology_euler_eq V hfinite]
  exact finsum_congr (fun i => congrArg (fun n : ℕ => sign i * (n : ℤ)) (hrank i))

/-- Local bounded complexes of fixed term ranks give local constancy of Euler values. -/
theorem locally_constant_of_complexes {X : Type*} [TopologicalSpace X] (f : X → ℚ)
    (hlocal : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ r : ℤ → ℕ, Function.HasFiniteSupport r ∧
      ∃ V : U → CochainComplex (ModuleCat.{u} K) ℤ,
        (∀ z i, Module.Finite K ((V z).X i)) ∧
        (∀ z i, Module.finrank K ((V z).X i) = r i) ∧
        (∀ z : U, f z.val = ((V z).homologyEulerChar : ℚ))) :
    IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_exists_open f).mpr
  intro x
  obtain ⟨U, hU, hx, r, hr, V, hfinite, hrank, hvalue⟩ := hlocal x
  have hconst : ∀ z : U, f z.val = ((∑ᶠ i, sign i * (r i : ℤ) : ℤ) : ℚ) := by
    intro z
    let : ∀ i, Module.Finite K ((V z).X i) := hfinite z
    rw [hvalue z, homology_euler_of_ranks (V z) r hr (hrank z)]
  exact ⟨U, hU, hx, fun y hy => (hconst ⟨y, hy⟩).trans (hconst ⟨x, hx⟩).symm⟩

end PhilipponMultiplicity.ComplexEuler
end

end


section
set_option autoImplicit false
open scoped BigOperators Topology
noncomputable section
universe u
namespace PhilipponMultiplicity

theorem connected_family_model_of_local_complexes
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val))
    (hgeometry : ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module ℤ L)
      (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : L →ₗ[ℤ] A), Function.Surjective q ∧
      ∃ (ρ : Multiplicative G.Point →* (L ≃ₗ[ℤ] L)) (c : G.FactorIndex → L),
        (∀ g x, q x = 0 → q (ρ g x) = 0) ∧
        ∃ (C : Type u) (σ : Multiplicative L →* Equiv.Perm C)
          (d : C → ℕ) (e : C → ℚ) (S : C → C → Option C → Prop),
          (∀ l a b Q, S a b Q → S (σ l a) (σ l b) (Q.map (σ l))) ∧
          (∀ a b Q, S a b Q → e b = e a + Q.elim 0 e) ∧
          (∀ l a, ∃ (k : C) (Q Q' : Option C),
            S k a Q ∧ S k (σ (Multiplicative.ofAdd l) a) Q' ∧
            (∀ b ∈ Q, d b < d a) ∧ (∀ b ∈ Q', d b < d a)) ∧
          (∃ (ι : Type u) (X : ι → Type u) (top : ∀ i, TopologicalSpace (X i))
            (s t : ∀ i, X i) (p : ∀ i, X i → L),
            (∀ i, @ConnectedSpace (X i) (top i)) ∧
            (∀ i a x, ∃ U : Set (X i), @IsOpen (X i) (top i) U ∧ x ∈ U ∧
              ∃ r : ℤ → ℕ, Function.HasFiniteSupport r ∧
              ∃ V : U → CochainComplex (ModuleCat.{u} K) ℤ,
                (∀ z j, Module.Finite K ((V z).X j)) ∧
                (∀ z j, Module.finrank K ((V z).X j) = r j) ∧
                (∀ z : U, e (σ (Multiplicative.ofAdd (p i z.val)) a) =
                  ((V z).homologyEulerChar : ℚ))) ∧
            LinearMap.ker q =
              Submodule.span ℤ (Set.range (fun i => p i (t i) - p i (s i)))) ∧
          ∀ (V : Set (groupProjectiveClosure G)),
            @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
            ∃ a : C,
              d a ≤ SectionThree.locusDimension G.ambient (Subtype.val '' V) ∧
              ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
                ∃ N : ℕ, ∀ n ≥ N,
                  e (σ (Multiplicative.ofAdd
                    (n • ρ (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i))) a) =
                    (Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
                      (G.ambient.vanishingIdeal (Subtype.val '' (τ g '' V)))
                      (fun i => D i * n) : ℚ)) :
    ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module ℤ L)
      (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : L →ₗ[ℤ] A), Function.Surjective q ∧
      ∃ (ρ : Multiplicative G.Point →* (L ≃ₗ[ℤ] L)) (c : G.FactorIndex → L),
        (∀ g x, q x = 0 → q (ρ g x) = 0) ∧
        ∃ (C : Type u) (σ : Multiplicative L →* Equiv.Perm C)
          (d : C → ℕ) (e : C → ℚ) (S : C → C → Option C → Prop),
          (∀ l a b Q, S a b Q → S (σ l a) (σ l b) (Q.map (σ l))) ∧
          (∀ a b Q, S a b Q → e b = e a + Q.elim 0 e) ∧
          (∀ l a, ∃ (k : C) (Q Q' : Option C),
            S k a Q ∧ S k (σ (Multiplicative.ofAdd l) a) Q' ∧
            (∀ b ∈ Q, d b < d a) ∧ (∀ b ∈ Q', d b < d a)) ∧
          (∃ (ι : Type u) (X : ι → Type u) (top : ∀ i, TopologicalSpace (X i))
            (s t : ∀ i, X i) (p : ∀ i, X i → L),
            (∀ i, @ConnectedSpace (X i) (top i)) ∧
            (∀ i a, @IsLocallyConstant (X i) ℚ (top i)
              (fun x => e (σ (Multiplicative.ofAdd (p i x)) a))) ∧
            LinearMap.ker q =
              Submodule.span ℤ (Set.range (fun i => p i (t i) - p i (s i)))) ∧
          ∀ (V : Set (groupProjectiveClosure G)),
            @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
            ∃ a : C,
              d a ≤ SectionThree.locusDimension G.ambient (Subtype.val '' V) ∧
              ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
                ∃ N : ℕ, ∀ n ≥ N,
                  e (σ (Multiplicative.ofAdd
                    (n • ρ (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i))) a) =
                    (Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
                      (G.ambient.vanishingIdeal (Subtype.val '' (τ g '' V)))
                      (fun i => D i * n) : ℚ) := by
  classical
  obtain ⟨L, hL, hML, A, hA, hMA, hFA, q, hq, ρ, c, hker,
    C, σ, d, e, S, hS, he, hcommon, hfam, hV⟩ := hgeometry
  obtain ⟨ι, X, top, s, t, p, hconn, hlocal, hspan⟩ := hfam
  refine ⟨L, hL, hML, A, hA, hMA, hFA, q, hq, ρ, c, hker,
    C, σ, d, e, S, hS, he, hcommon,
    ⟨ι, X, top, s, t, p, hconn, ?_, hspan⟩, hV⟩
  intro i a
  let : TopologicalSpace (X i) := top i
  exact ComplexEuler.locally_constant_of_complexes
    (fun x => e (σ (Multiplicative.ofAdd (p i x)) a)) (hlocal i a)

end PhilipponMultiplicity
end

end

set_option autoImplicit false
open PhilipponMultiplicity
open scoped BigOperators Topology
universe u

theorem solution
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val)) :
    ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module ℤ L)
      (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : L →ₗ[ℤ] A), Function.Surjective q ∧
      ∃ (ρ : Multiplicative G.Point →* (L ≃ₗ[ℤ] L)) (c : G.FactorIndex → L),
        (∀ g x, q x = 0 → q (ρ g x) = 0) ∧
        ∃ (C : Type u) (σ : Multiplicative L →* Equiv.Perm C)
          (d : C → ℕ) (e : C → ℚ) (S : C → C → Option C → Prop),
          (∀ l a b Q, S a b Q → S (σ l a) (σ l b) (Q.map (σ l))) ∧
          (∀ a b Q, S a b Q → e b = e a + Q.elim 0 e) ∧
          (∀ l a, ∃ (k : C) (Q Q' : Option C),
            S k a Q ∧ S k (σ (Multiplicative.ofAdd l) a) Q' ∧
            (∀ b ∈ Q, d b < d a) ∧ (∀ b ∈ Q', d b < d a)) ∧
          (∃ (ι : Type u) (X : ι → Type u) (top : ∀ i, TopologicalSpace (X i))
            (s t : ∀ i, X i) (p : ∀ i, X i → L),
            (∀ i, @ConnectedSpace (X i) (top i)) ∧
            (∀ i a, @IsLocallyConstant (X i) ℚ (top i)
              (fun x => e (σ (Multiplicative.ofAdd (p i x)) a))) ∧
            LinearMap.ker q =
              Submodule.span ℤ (Set.range (fun i => p i (t i) - p i (s i)))) ∧
          ∀ (V : Set (groupProjectiveClosure G)),
            @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
            ∃ a : C,
              d a ≤ SectionThree.locusDimension G.ambient (Subtype.val '' V) ∧
              ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
                ∃ N : ℕ, ∀ n ≥ N,
                  e (σ (Multiplicative.ofAdd
                    (n • ρ (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i))) a) =
                    (Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
                      (G.ambient.vanishingIdeal (Subtype.val '' (τ g '' V)))
                      (fun i => D i * n) : ℚ) := by
  exact connected_family_model_of_local_complexes K hK G τ hzero hadd hregular
    (closure_action_has_local_complex_model K hK G τ hzero hadd hregular)
