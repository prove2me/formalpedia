-- Prove2me | solution 1 for UAVariety.quot_iInf_mem_SP
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T17:14:48.242194+00:00
-- url     : https://prove2.me/submissions/58cdfe1e-85fc-443e-96f5-544d2c9dc44c

import Definitions.Def_UAVariety_defs

universe u₁ v₁

set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic]

theorem fsp_quot_iInf_mem_SP (K : Set (Alg L)) {M : Type u₁} [L.Structure M] {ι : Type u₁}
    (φ : ι → Congruence (L := L) M) (hφ : ∀ i, Alg.of (φ i).Quot ∈ K)
    (θ : Congruence (L := L) M) (hθ : ∀ a b, θ.r a b ↔ ∀ i, (φ i).r a b) :
    Alg.of θ.Quot ∈ S (P K) := by
  refine ⟨Alg.of (∀ i, (φ i).Quot), ⟨ι, fun i => Alg.of (φ i).Quot, hφ, ⟨Language.Equiv.refl L _⟩⟩, ?_⟩
  let g : θ.Quot → ∀ i, (φ i).Quot :=
    Quotient.lift (fun a i => Quotient.mk (φ i).toSetoid a)
      (fun a b h => funext fun i => Quotient.sound ((hθ a b).1 h i))
  refine ⟨⟨⟨g, ?_⟩, ?_, fun r => isEmptyElim r⟩⟩
  · intro p q hpq
    induction p using Quotient.ind
    induction q using Quotient.ind
    exact Quotient.sound ((hθ _ _).2 fun i => Quotient.exact (congrFun hpq i))
  · intro n f x
    have hx : x = fun j => Quotient.mk θ.toSetoid ((x j).out) :=
      funext fun j => (Quotient.out_eq _).symm
    rw [hx]
    show g (Structure.funMap f fun j => Quotient.mk θ.toSetoid ((x j).out)) = _
    rw [funMap_quotient_mk']
    funext i
    show Quotient.mk (φ i).toSetoid _ = Structure.funMap f (fun j => Quotient.mk (φ i).toSetoid ((x j).out))
    rw [funMap_quotient_mk']

end UAVariety

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] (K : Set (UAVariety.Alg L)) {M : Type u₁} [L.Structure M] {ι : Type u₁}
    (φ : ι → UAVariety.Congruence (L := L) M) (hφ : ∀ i, UAVariety.Alg.of (φ i).Quot ∈ K)
    (θ : UAVariety.Congruence (L := L) M) (hθ : ∀ a b, θ.r a b ↔ ∀ i, (φ i).r a b) :
    UAVariety.Alg.of θ.Quot ∈ UAVariety.S (UAVariety.P K) :=
  UAVariety.fsp_quot_iInf_mem_SP K φ hφ θ hθ
