-- Prove2me | solution 1 for PhilipponMultiplicity.closure_action_has_coherent_generator_presentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-09T01:42:08.684951+00:00
-- url     : https://prove2.me/submissions/61724b4a-2736-43b5-9a4b-49766579ee8d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_closure_action_has_coherent_exact_sequence_model
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_Support
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Abel


section

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.CoherentExact
variable {C : Type*}

/-- An absent cokernel contributes the zero vector, including in dimension zero. -/
def optionalVector (Q : Option C) : C →₀ ℤ :=
  Q.elim 0 (fun a => Finsupp.single a 1)

def relation (a b : C) (Q : Option C) : C →₀ ℤ :=
  Finsupp.single b 1 - Finsupp.single a 1 - optionalVector Q

def relations (S : C → C → Option C → Prop) : Submodule ℤ (C →₀ ℤ) :=
  Submodule.span ℤ {r | ∃ a b Q, S a b Q ∧ r = relation a b Q}

theorem relation_mem (S : C → C → Option C → Prop) (a b : C) (Q : Option C)
    (h : S a b Q) : relation a b Q ∈ relations S :=
  Submodule.subset_span ⟨a, b, Q, h, rfl⟩

theorem map_optionalVector (f : C → C) (Q : Option C) :
    Finsupp.lmapDomain ℤ ℤ f (optionalVector Q) = optionalVector (Q.map f) := by
  cases Q <;> simp [optionalVector]

theorem map_relation (f : C → C) (a b : C) (Q : Option C) :
    Finsupp.lmapDomain ℤ ℤ f (relation a b Q) = relation (f a) (f b) (Q.map f) := by
  simp only [relation, map_sub]
  rw [map_optionalVector]
  simp

/-- Preservation of individual exact triples extends to their full relation submodule. -/
theorem relations_stable (S : C → C → Option C → Prop) (f : C → C)
    (hf : ∀ a b Q, S a b Q → S (f a) (f b) (Q.map f))
    (v : C →₀ ℤ) (hv : v ∈ relations S) :
    Finsupp.lmapDomain ℤ ℤ f v ∈ relations S := by
  apply (Submodule.span_le (p := (relations S).comap (Finsupp.lmapDomain ℤ ℤ f))).mpr ?_ hv
  rintro r ⟨a, b, Q, hS, rfl⟩
  change Finsupp.lmapDomain ℤ ℤ f (relation a b Q) ∈ relations S
  rw [map_relation]
  exact relation_mem S _ _ _ (hf a b Q hS)

theorem euler_optionalVector (e : C → ℚ) (Q : Option C) :
    Finsupp.linearCombination ℤ e (optionalVector Q) = Q.elim 0 e := by
  cases Q <;> simp [optionalVector]

/-- Euler additivity on exact triples annihilates every generated relation. -/
theorem euler_relations (S : C → C → Option C → Prop) (e : C → ℚ)
    (he : ∀ a b Q, S a b Q → e b = e a + Q.elim 0 e)
    (v : C →₀ ℤ) (hv : v ∈ relations S) : Finsupp.linearCombination ℤ e v = 0 := by
  apply (Submodule.span_le (p := LinearMap.ker (Finsupp.linearCombination ℤ e))).mpr ?_ hv
  rintro r ⟨a, b, Q, hS, rfl⟩
  change Finsupp.linearCombination ℤ e (relation a b Q) = 0
  simp only [relation, map_sub, Finsupp.linearCombination_single, one_smul, euler_optionalVector]
  rw [he a b Q hS]
  abel

theorem optionalVector_support (d : C → ℕ) (n : ℕ) (Q : Option C)
    (hQ : ∀ a ∈ Q, d a < n) : ∀ a ∈ (optionalVector Q).support, d a < n := by
  intro a ha
  cases Q with
  | none => simp [optionalVector] at ha
  | some b =>
    have hab : a = b := Finset.mem_singleton.mp (Finsupp.support_single_subset ha)
    subst a
    exact hQ b (by simp)

/-- Subtracting two exact sequences with the same source gives a lower-support relation. -/
theorem common_source_difference (S : C → C → Option C → Prop) (d : C → ℕ)
    (a a' k : C) (Q Q' : Option C) (hQ : S k a Q) (hQ' : S k a' Q')
    (hdQ : ∀ b ∈ Q, d b < d a) (hdQ' : ∀ b ∈ Q', d b < d a) :
    ∃ w : C →₀ ℤ, (∀ b ∈ w.support, d b < d a) ∧
      Finsupp.single a' 1 - Finsupp.single a 1 - w ∈ relations S := by
  classical
  refine ⟨optionalVector Q' - optionalVector Q, ?_, ?_⟩
  · intro b hb
    have hmem := Finsupp.support_sub hb
    rcases Finset.mem_union.mp hmem with h | h
    · exact optionalVector_support d (d a) Q' hdQ' b h
    · exact optionalVector_support d (d a) Q hdQ b h
  · have h := (relations S).sub_mem (relation_mem S k a' Q' hQ') (relation_mem S k a Q hQ)
    convert h using 1
    simp only [relation]
    abel

end PhilipponMultiplicity.CoherentExact
end

end


section
set_option autoImplicit false
open scoped BigOperators Topology
noncomputable section
universe u
namespace PhilipponMultiplicity

theorem coherent_presentation_of_exact_sequences
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
          (∀ l, q l = 0 → ∀ a, e (σ (Multiplicative.ofAdd l) a) = e a) ∧
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
          (d : C → ℕ) (R : Submodule ℤ (C →₀ ℤ)) (e : C → ℚ),
          (∀ l v, v ∈ R → Finsupp.lmapDomain ℤ ℤ (σ l) v ∈ R) ∧
          (∀ v ∈ R, Finsupp.linearCombination ℤ e v = 0) ∧
          (∀ l a, ∃ w : C →₀ ℤ,
            (∀ b ∈ w.support, d b < d a) ∧
            Finsupp.single (σ (Multiplicative.ofAdd l) a) 1 -
              Finsupp.single a 1 - w ∈ R) ∧
          (∀ l, q l = 0 → ∀ a, e (σ (Multiplicative.ofAdd l) a) = e a) ∧
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
    C, σ, d, e, S, hS, he, hcommon, hEuler, hV⟩ := hgeometry
  refine ⟨L, hL, hML, A, hA, hMA, hFA, q, hq, ρ, c, hker,
    C, σ, d, CoherentExact.relations S, e, ?_, ?_, ?_, hEuler, hV⟩
  · intro l v hv
    exact CoherentExact.relations_stable S (σ l) (hS l) v hv
  · exact CoherentExact.euler_relations S e he
  · intro l a
    obtain ⟨k, Q, Q', hQ, hQ', hdQ, hdQ'⟩ := hcommon l a
    exact CoherentExact.common_source_difference S d a (σ (Multiplicative.ofAdd l) a)
      k Q Q' hQ hQ' hdQ hdQ'

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
          (d : C → ℕ) (R : Submodule ℤ (C →₀ ℤ)) (e : C → ℚ),
          (∀ l v, v ∈ R → Finsupp.lmapDomain ℤ ℤ (σ l) v ∈ R) ∧
          (∀ v ∈ R, Finsupp.linearCombination ℤ e v = 0) ∧
          (∀ l a, ∃ w : C →₀ ℤ,
            (∀ b ∈ w.support, d b < d a) ∧
            Finsupp.single (σ (Multiplicative.ofAdd l) a) 1 -
              Finsupp.single a 1 - w ∈ R) ∧
          (∀ l, q l = 0 → ∀ a, e (σ (Multiplicative.ofAdd l) a) = e a) ∧
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
  exact coherent_presentation_of_exact_sequences K hK G τ hzero hadd hregular
    (closure_action_has_coherent_exact_sequence_model K hK G τ hzero hadd hregular)
