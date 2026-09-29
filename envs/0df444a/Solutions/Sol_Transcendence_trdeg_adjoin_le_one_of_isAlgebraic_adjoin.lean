-- Prove2me | solution 1 for Transcendence.trdeg_adjoin_le_one_of_isAlgebraic_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T18:03:49.569788+00:00
-- url     : https://prove2.me/submissions/1cb70071-c13f-4bc6-abcb-66da64fe7084

import Mathlib

namespace P17_trdeg

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

-- A subalgebra containing `x`, all of whose elements are algebraic over `K[x]`, has
-- transcendence degree at most one.
theorem trdeg_le_one_of_adjoin_singleton
    {B : Subalgebra K L} {x : L} (hxB : x ∈ B)
    (halg : ∀ y ∈ B, IsAlgebraic ↥(Algebra.adjoin K ({x} : Set L)) y) :
    Algebra.trdeg K ↥B ≤ 1 := by
  set x' : (↥B) := ⟨x, hxB⟩ with hx'
  have hmap : Subalgebra.map B.val (Algebra.adjoin K ({x'} : Set ↥B))
      = Algebra.adjoin K ({x} : Set L) := by
    rw [AlgHom.map_adjoin]
    congr 1
    simp [hx']
  let e : ↥(Algebra.adjoin K ({x'} : Set ↥B)) ≃ₐ[K] ↥(Algebra.adjoin K ({x} : Set L)) :=
    (Subalgebra.equivMapOfInjective _ B.val Subtype.val_injective).trans
      (Subalgebra.equivOfEq _ _ hmap)
  have : Algebra.IsAlgebraic ↥(Algebra.adjoin K ({x'} : Set ↥B)) ↥B := by
    constructor
    intro y
    refine IsAlgebraic.of_ringHom_of_comp_eq (f := (e : _ →+* _))
      (g := (B.val : ↥B →+* L)) (halg y y.2) e.surjective Subtype.val_injective ?_
    ext c
    rfl
  simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk K ({x'} : Set ↥B)

-- The elements of `L` algebraic over `K[x]`, as a `K`-subalgebra of `L`.
noncomputable def E (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (x : L) :
    Subalgebra K L :=
  (Subalgebra.algebraicClosure ↥(Algebra.adjoin K ({x} : Set L)) L).restrictScalars K

theorem mem_E_iff {x z : L} : z ∈ E K x ↔ IsAlgebraic ↥(Algebra.adjoin K ({x} : Set L)) z :=
  Iff.rfl

theorem self_mem_E (x : L) : x ∈ E K x := by
  rw [mem_E_iff]
  have h : x = algebraMap ↥(Algebra.adjoin K ({x} : Set L)) L
      ⟨x, Algebra.subset_adjoin rfl⟩ := rfl
  rw [h]
  exact isAlgebraic_algebraMap _

theorem trdeg_le_one_of_le_E {B : Subalgebra K L} {x : L} (h : B ≤ E K x) :
    Algebra.trdeg K ↥B ≤ 1 :=
  (trdeg_le_of_injective (Subalgebra.inclusion h) (Subalgebra.inclusion_injective h)).trans
    (trdeg_le_one_of_adjoin_singleton (self_mem_E x) (fun _ hy => hy))

end P17_trdeg

open P17_trdeg in
theorem solution {K L : Type*} [Field K] [Field L]
    [Algebra K L] (x : L) (S : Set L)
    (hS : ∀ s ∈ S, IsAlgebraic ↥(Algebra.adjoin K ({x} : Set L)) s) :
    Algebra.trdeg K ↥(Algebra.adjoin K S) ≤ 1 := by
  exact trdeg_le_one_of_le_E (x := x) (Algebra.adjoin_le fun s hs => mem_E_iff.2 (hS s hs))

#print axioms solution
