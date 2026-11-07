-- Prove2me | solution 1 for UAVariety.same_identities
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T16:22:24.272918+00:00
-- url     : https://prove2.me/submissions/fb0085a6-62ba-4925-ab2a-6007cc0d1653

import Definitions.Def_UAVariety_defs

universe u₁ v₁ w₁

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u₁, v₁}}

/-- Terms in a direct product are realized coordinatewise. -/
theorem si_realize_pi {X : Type w₁} {ι : Type u₁} (A : ι → Alg L) (t : L.Term X)
    (v : X → ∀ i, A i) (i : ι) :
    t.realize v i = t.realize (fun x => v x i) := by
  induction t with
  | var x => rfl
  | func f ts ih =>
    show (Structure.funMap f (fun j => (ts j).realize v) : ∀ i, A i) i = _
    simp only [Term.realize]
    show Structure.funMap f (fun j => (ts j).realize v i) = _
    simp only [ih]

theorem si_H {K : Set (Alg L)} {X : Type w₁} (p q : L.Term X)
    (h : ∀ A ∈ K, Satisfies A (p, q)) : ∀ B ∈ H K, Satisfies B (p, q) := by
  rintro B ⟨A, hA, f, hf⟩ v
  obtain ⟨w', hw⟩ : ∃ w' : X → A, f ∘ w' = v :=
    ⟨fun x => (hf (v x)).choose, funext fun x => (hf (v x)).choose_spec⟩
  subst hw
  simp only [HomClass.realize_term]
  exact congrArg f (h A hA w')

theorem si_S {K : Set (Alg L)} {X : Type w₁} (p q : L.Term X)
    (h : ∀ A ∈ K, Satisfies A (p, q)) : ∀ B ∈ S K, Satisfies B (p, q) := by
  rintro B ⟨A, hA, ⟨f⟩⟩ v
  apply f.injective
  have := h A hA (f ∘ v)
  simpa only [HomClass.realize_term] using this

theorem si_P {K : Set (Alg L)} {X : Type w₁} (p q : L.Term X)
    (h : ∀ A ∈ K, Satisfies A (p, q)) : ∀ B ∈ P K, Satisfies B (p, q) := by
  rintro B ⟨ι, A, hA, ⟨e⟩⟩ v
  apply e.injective
  have key : p.realize (e ∘ v) = q.realize (e ∘ v) := by
    funext i
    rw [si_realize_pi, si_realize_pi]
    exact h (A i) (hA i) _
  simpa only [HomClass.realize_term] using key

/-- `A ≅ A^PUnit`. -/
def si_unitEquiv (A : Alg L) : A ≃[L] ∀ _ : PUnit.{u₁ + 1}, A where
  toEquiv := (Equiv.funUnique PUnit.{u₁ + 1} A).symm
  map_fun' f x := by funext i; rfl
  map_rel' r x := ⟨fun h => h PUnit.unit, fun h _ => h⟩

theorem si_sub_H (K : Set (Alg L)) : K ⊆ H K :=
  fun A hA => ⟨A, hA, Hom.id L A, Function.surjective_id⟩

theorem si_sub_S (K : Set (Alg L)) : K ⊆ S K :=
  fun A hA => ⟨A, hA, ⟨Embedding.refl L A⟩⟩

theorem si_sub_P (K : Set (Alg L)) : K ⊆ P K :=
  fun A hA => ⟨PUnit.{u₁ + 1}, fun _ => A, fun _ => hA, ⟨si_unitEquiv A⟩⟩

theorem si_sub_V (K : Set (Alg L)) : K ⊆ V K :=
  fun _ hA _ hW => hW.2 hA

theorem si_V {K : Set (Alg L)} {X : Type w₁} (p q : L.Term X)
    (h : ∀ A ∈ K, Satisfies A (p, q)) : ∀ B ∈ V K, Satisfies B (p, q) := by
  intro B hB
  let W : Set (Alg L) := {A | Satisfies A (p, q)}
  have hW : IsVariety W :=
    ⟨fun A hA => si_H (K := W) p q (fun _ h => h) A hA,
     fun A hA => si_S (K := W) p q (fun _ h => h) A hA,
     fun A hA => si_P (K := W) p q (fun _ h => h) A hA⟩
  exact hB W ⟨hW, h⟩

theorem si_main (K : Set (Alg L)) {X : Type w₁} (p q : L.Term X) :
    ((∀ A ∈ H K, Satisfies A (p, q)) ↔ ∀ A ∈ K, Satisfies A (p, q)) ∧
      ((∀ A ∈ S K, Satisfies A (p, q)) ↔ ∀ A ∈ K, Satisfies A (p, q)) ∧
      ((∀ A ∈ P K, Satisfies A (p, q)) ↔ ∀ A ∈ K, Satisfies A (p, q)) ∧
      ((∀ A ∈ V K, Satisfies A (p, q)) ↔ ∀ A ∈ K, Satisfies A (p, q)) :=
  ⟨⟨fun h A hA => h A (si_sub_H K hA), si_H p q⟩,
   ⟨fun h A hA => h A (si_sub_S K hA), si_S p q⟩,
   ⟨fun h A hA => h A (si_sub_P K hA), si_P p q⟩,
   ⟨fun h A hA => h A (si_sub_V K hA), si_V p q⟩⟩

end UAVariety

open UAVariety in
theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic]
    (K : Set (Alg L)) {X : Type w₁} (p q : L.Term X) :
    ((∀ A ∈ H K, Satisfies A (p, q)) ↔ ∀ A ∈ K, Satisfies A (p, q)) ∧
      ((∀ A ∈ S K, Satisfies A (p, q)) ↔ ∀ A ∈ K, Satisfies A (p, q)) ∧
      ((∀ A ∈ P K, Satisfies A (p, q)) ↔ ∀ A ∈ K, Satisfies A (p, q)) ∧
      ((∀ A ∈ V K, Satisfies A (p, q)) ↔ ∀ A ∈ K, Satisfies A (p, q)) :=
  si_main K p q
