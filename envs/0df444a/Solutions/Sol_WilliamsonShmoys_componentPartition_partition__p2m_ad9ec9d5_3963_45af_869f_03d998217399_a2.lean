-- Prove2me | solution 1 for WilliamsonShmoys.componentPartition_partition__p2m_ad9ec9d5_3963_45af_869f_03d998217399_a2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-10T17:23:53.280594+00:00
-- url     : https://prove2.me/submissions/2cd8256f-9d44-4e96-8fb0-4c8a9dcea0ba

import Mathlib

open scoped BigOperators

set_option autoImplicit false

/-- Every finite graph's vertex set admits a partition into connected blocks (for instance the
singletons), indexed as a `Finset (Finset V)`. -/
theorem solution {V : Type*} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (dL : DecidableRel L.Adj) :
    letI : DecidableRel L.Adj := dL
    ∃ C : Finset (Finset V),
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃ s ∈ C, v ∈ s) ∧
      (∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t) ∧
      (∑ s ∈ C, s.card) = Fintype.card V ∧
      (∀ s ∈ C, (L.induce (↑s : Set V)).Connected) := by
  classical
  let C : Finset (Finset V) := Finset.univ.image (fun v : V => ({v} : Finset V))
  refine ⟨C, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hs
    simp
  · intro v
    exact ⟨{v}, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩, by simp⟩
  · intro s hs t ht hne
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp ht
    have hvw : v ≠ w := by simpa using hne
    rw [Finset.disjoint_singleton_left]
    simpa using hvw
  · have hcard : C.card = Fintype.card V := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro v w h
        simpa using h
    have h1 : ∀ s ∈ C, s.card = 1 := by
      intro s hs
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hs
      simp
    rw [Finset.sum_congr rfl h1]
    simp [hcard]
  · intro s hs
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hs
    haveI : Nonempty (↥(↑({v} : Finset V) : Set V)) := ⟨⟨v, by simp⟩⟩
    refine SimpleGraph.Connected.mk ?_
    intro x y
    have hx : x = y := by
      apply Subtype.ext
      have h1 : x.val = v := by simpa using x.property
      have h2 : y.val = v := by simpa using y.property
      rw [h1, h2]
    rw [hx]
