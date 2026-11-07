-- Prove2me | solution 1 for UAVariety.P_H_subset_H_P
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T16:42:33.736248+00:00
-- url     : https://prove2.me/submissions/f68a273d-3e6e-42db-b914-a75b1737451a

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

theorem hsp_P_H_subset_H_P_main (K : Set (Alg L)) : P (H K) ⊆ H (P K) := by
  rintro B ⟨ι, A, hA, ⟨e⟩⟩
  choose C hC f hf using hA
  refine ⟨Alg.of (∀ i, C i), ⟨ι, C, hC, ⟨Language.Equiv.refl L _⟩⟩,
    e.symm.toHom.comp (hsp_piHom f), ?_⟩
  intro b
  refine ⟨fun i => (hf i (e b i)).choose, ?_⟩
  have hx : hsp_piHom f (fun i => (hf i (e b i)).choose) = e b :=
    funext fun i => (hf i (e b i)).choose_spec
  show e.symm (hsp_piHom f _) = b
  rw [hx]
  exact e.symm_apply_apply b

end UAVariety

open UAVariety in
theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] (K : Set (Alg L)) :
    P (H K) ⊆ H (P K) :=
  hsp_P_H_subset_H_P_main K
