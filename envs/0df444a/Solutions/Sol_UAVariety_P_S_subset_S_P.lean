-- Prove2me | solution 1 for UAVariety.P_S_subset_S_P
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T16:42:32.675832+00:00
-- url     : https://prove2.me/submissions/8f815bf3-7f08-42ae-8fd5-d866ff02eba8

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

theorem hsp_P_S_subset_S_P_main (K : Set (Alg L)) : P (S K) ⊆ S (P K) := by
  rintro B ⟨ι, A, hA, ⟨e⟩⟩
  choose C hC g using hA
  exact ⟨Alg.of (∀ i, C i), ⟨ι, C, hC, ⟨Language.Equiv.refl L _⟩⟩,
    ⟨(hsp_piEmb fun i => (g i).some).comp e.toEmbedding⟩⟩

end UAVariety

open UAVariety in
theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] (K : Set (Alg L)) :
    P (S K) ⊆ S (P K) :=
  hsp_P_S_subset_S_P_main K
