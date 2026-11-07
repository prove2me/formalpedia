-- Prove2me | solution 1 for UAVariety.S_H_subset_H_S
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T16:42:31.573658+00:00
-- url     : https://prove2.me/submissions/5c49af9f-8af2-4f31-bba5-c91719a8a2c4

import Definitions.Def_UAVariety_defs

universe u₁ v₁

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic]

/-! ### Product constructions -/

/-- Coordinatewise homomorphism between products. -/
def hsp_piHom {ι : Type*} {M N : ι → Type*} [∀ i, L.Structure (M i)] [∀ i, L.Structure (N i)]
    (f : ∀ i, M i →[L] N i) : (∀ i, M i) →[L] ∀ i, N i where
  toFun x i := f i (x i)
  map_fun' g x := by
    funext i
    exact (f i).map_fun g (fun j => x j i)
  map_rel' r := isEmptyElim r

/-- Coordinatewise embedding between products. -/
def hsp_piEmb {ι : Type*} {M N : ι → Type*} [∀ i, L.Structure (M i)] [∀ i, L.Structure (N i)]
    (f : ∀ i, M i ↪[L] N i) : (∀ i, M i) ↪[L] ∀ i, N i where
  toFun x i := f i (x i)
  inj' x y h := funext fun i => (f i).injective (congrFun h i)
  map_fun' g x := by
    funext i
    exact (f i).map_fun g (fun j => x j i)
  map_rel' r := isEmptyElim r

/-- Coordinatewise isomorphism between products. -/
def hsp_piEquiv {ι : Type*} {M N : ι → Type*} [∀ i, L.Structure (M i)] [∀ i, L.Structure (N i)]
    (f : ∀ i, M i ≃[L] N i) : (∀ i, M i) ≃[L] ∀ i, N i where
  toEquiv := Equiv.piCongrRight fun i => (f i).toEquiv
  map_fun' g x := by
    funext i
    exact (f i).map_fun g (fun j => x j i)
  map_rel' r := isEmptyElim r

/-- A product of products is a product over the sigma type. -/
def hsp_piSigma {ι : Type*} {κ : ι → Type*} (C : ∀ i, κ i → Type*)
    [∀ i j, L.Structure (C i j)] :
    (∀ i, ∀ j, C i j) ≃[L] ∀ p : Σ i, κ i, C p.1 p.2 where
  toEquiv := (Equiv.piCurry C).symm
  map_fun' g x := rfl
  map_rel' r := isEmptyElim r

theorem hsp_S_H_subset_H_S_main (K : Set (Alg L)) : S (H K) ⊆ H (S K) := by
  rintro B ⟨C, ⟨A, hA, f, hf⟩, ⟨g⟩⟩
  let D : L.Substructure A := g.toHom.range.comap f
  have hD : ∀ x : D, f x ∈ g.toHom.range := fun x => x.2
  refine ⟨Alg.of D, ⟨A, hA, ⟨D.subtype⟩⟩,
    g.equivRange.symm.toHom.comp (Hom.codRestrict (g.toHom.range) (f.comp D.subtype.toHom) hD), ?_⟩
  intro b
  obtain ⟨a, ha⟩ := hf (g b)
  have haD : a ∈ D := by
    show f a ∈ g.toHom.range
    exact ha ▸ Hom.mem_range_self _ b
  refine ⟨⟨a, haD⟩, ?_⟩
  show g.equivRange.symm _ = b
  apply g.equivRange.injective
  rw [Language.Equiv.apply_symm_apply]
  apply Subtype.ext
  show f a = g b
  exact ha

end UAVariety

open UAVariety in
theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] (K : Set (Alg L)) :
    S (H K) ⊆ H (S K) :=
  hsp_S_H_subset_H_S_main K
