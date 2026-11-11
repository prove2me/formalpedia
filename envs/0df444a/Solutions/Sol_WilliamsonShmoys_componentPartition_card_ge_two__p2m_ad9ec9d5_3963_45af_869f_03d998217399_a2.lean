-- Prove2me | solution 1 for WilliamsonShmoys.componentPartition_card_ge_two__p2m_ad9ec9d5_3963_45af_869f_03d998217399_a2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-10T17:45:47.760952+00:00
-- url     : https://prove2.me/submissions/910294c4-bb30-40aa-92bf-913f771386d8

import Mathlib

open scoped BigOperators

set_option autoImplicit false

/-- A disconnected graph on at least three vertices cannot be covered by connected blocks with only
one block. -/
theorem solution {V : Type*} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (dL : DecidableRel L.Adj) (hconn : ¬ L.Connected) (hn : 3 ≤ Fintype.card V)
    (C : Finset (Finset V)) (hne : ∀ s ∈ C, s.Nonempty)
    (hcover : ∀ v : V, ∃ s ∈ C, v ∈ s)
    (hCconn : ∀ s ∈ C, (L.induce (↑s : Set V)).Connected) : 2 ≤ C.card := by
  classical
  by_contra h
  have hc1 : C.card ≤ 1 := by omega
  have hpos : 0 < C.card := by
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
    obtain ⟨s, hs, -⟩ := hcover v
    exact Finset.card_pos.mpr ⟨s, hs⟩
  have hc : C.card = 1 := by omega
  obtain ⟨s, rfl⟩ := Finset.card_eq_one.mp hc
  have huniv : s = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    obtain ⟨t, ht, hvt⟩ := hcover v
    rw [Finset.mem_singleton] at ht
    rwa [ht] at hvt
  apply hconn
  have hsconn := hCconn s (Finset.mem_singleton_self s)
  have hpre : L.Preconnected := by
    intro u v
    have hu : u ∈ (↑s : Set V) := by
      rw [huniv]
      exact Finset.mem_univ u
    have hv : v ∈ (↑s : Set V) := by
      rw [huniv]
      exact Finset.mem_univ v
    have hwalk : (L.induce (↑s : Set V)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := hsconn _ _
    exact hwalk.map ⟨Subtype.val, fun {a b} h => h⟩
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  exact ⟨hpre⟩
