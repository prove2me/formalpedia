-- Prove2me | solution 1 for VapnikChervonenkis.Entropy.eq12_index_append_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:31:40.237436+00:00
-- url     : https://prove2.me/submissions/96f6a50f-ecf1-49ab-93ee-be65c3094320

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

theorem aux_eq12_main {X : Type*} (S : Set (Set X)) {k m : ℕ} (x : Fin k → X)
    (y : Fin m → X) :
    Shared.index S (Fin.append x y) ≤ Shared.index S x * Shared.index S y := by
  classical
  unfold Shared.index
  rw [← Finset.card_product]
  let f : Finset (Fin (k + m)) → Finset (Fin k) × Finset (Fin m) := fun t =>
    (Finset.univ.filter (fun i => Fin.castAdd m i ∈ t),
     Finset.univ.filter (fun j => Fin.natAdd k j ∈ t))
  apply Finset.card_le_card_of_injOn f
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht
    obtain ⟨A, hA, hAt⟩ := ht
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_prod, Set.mem_ofPred_eq, f]
    refine ⟨⟨A, hA, fun i => ?_⟩, ⟨A, hA, fun j => ?_⟩⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hAt, Fin.append_left]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hAt, Fin.append_right]
  · intro t1 _ t2 _ h
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    ext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · have := congrArg (fun s => a ∈ s) h1
      simpa using this
    · have := congrArg (fun s => b ∈ s) h2
      simpa using this

end VapnikChervonenkis.Entropy

open VapnikChervonenkis VapnikChervonenkis.Entropy
open MeasureTheory Filter Topology

theorem solution {X : Type*} (S : Set (Set X)) {k m : ℕ} (x : Fin k → X)
    (y : Fin m → X) :
    Shared.index S (Fin.append x y) ≤ Shared.index S x * Shared.index S y :=
  aux_eq12_main S x y
