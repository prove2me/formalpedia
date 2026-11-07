-- Prove2me | solution 1 for UAVariety.ker_quot_mem_S
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T16:55:30.709017+00:00
-- url     : https://prove2.me/submissions/ab58cd4e-0274-44eb-b027-e05f2e7913a0

import Definitions.Def_UAVariety_defs

universe u₁ v₁

set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic]

theorem fu_quot_lift_hom {M : Type*} [L.Structure M] {B : Type*} [L.Structure B]
    (φ : Congruence (L := L) M) (h : M →[L] B) (hφ : ∀ a b, φ.r a b → h a = h b) :
    ∃ g : φ.Quot →[L] B, ∀ a, g (Quotient.mk _ a) = h a := by
  refine ⟨⟨Quotient.lift h hφ, ?_, fun r => isEmptyElim r⟩, fun a => rfl⟩
  intro n f x
  have hx : x = fun i => Quotient.mk φ.toSetoid ((x i).out) :=
    funext fun i => (Quotient.out_eq _).symm
  rw [hx, funMap_quotient_mk']
  show h _ = _
  rw [h.map_fun]; rfl


theorem fu_ker_quot_mem_S (K : Set (Alg L)) {M : Type u₁} [L.Structure M] {A : Alg L}
    (hA : A ∈ K) (h : M →[L] A) :
    ∃ φ : Congruence (L := L) M, (∀ a b, φ.r a b ↔ h a = h b) ∧ Alg.of φ.Quot ∈ S K := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Congruence (L := L) M, ∀ a b, φ.r a b ↔ h a = h b := ⟨
    { r := fun a b => h a = h b
      iseqv := ⟨fun _ => rfl, fun e => e.symm, fun e₁ e₂ => e₁.trans e₂⟩
      fun_compat := fun f x y hxy => by
        rw [h.map_fun, h.map_fun]; congr 1; funext i; exact hxy i
      rel_compat := fun r => isEmptyElim r }, fun _ _ => Iff.rfl⟩
  refine ⟨φ, hφ, ?_⟩
  refine ⟨A, hA, ?_⟩
  obtain ⟨g, hg⟩ := fu_quot_lift_hom φ h (fun a b e => (hφ a b).1 e)
  refine ⟨⟨⟨g, ?_⟩, fun {n} f x => g.map_fun f x, fun r => isEmptyElim r⟩⟩
  intro p q hpq
  induction p using Quotient.ind
  induction q using Quotient.ind
  rw [hg, hg] at hpq
  exact Quotient.sound ((hφ _ _).2 hpq)

end UAVariety

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] (K : Set (UAVariety.Alg L)) {M : Type u₁} [L.Structure M] {A : UAVariety.Alg L}
    (hA : A ∈ K) (h : M →[L] A) :
    ∃ φ : UAVariety.Congruence (L := L) M, (∀ a b, φ.r a b ↔ h a = h b) ∧ UAVariety.Alg.of φ.Quot ∈ UAVariety.S K :=
  UAVariety.fu_ker_quot_mem_S K hA h
