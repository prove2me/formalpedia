-- Prove2me | solution 1 for WilliamsonShmoys.componentPartition_count__p2m_954faa17_a8ce_4e0c_b281_2379f22f5ab2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:06:48.460648+00:00
-- url     : https://prove2.me/submissions/c6a43342-2bc4-4b23-8b23-bc8857a455aa

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hconn : ¬ L.Connected)
    (hn : 3 ≤ Fintype.card V)
    (C : Finset (Finset V))
    (hnonempty : ∀ s ∈ C, s.Nonempty)
    (hcover : ∀ v : V, ∃ s ∈ C, v ∈ s)
    (hdisjoint : ∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t)
    (hconnected : ∀ s ∈ C, (L.induce (↑s : Set V)).Connected) :
    letI : DecidableRel L.Adj := dL
    2 ≤ C.card ∧ (∑ s ∈ C, s.card) = Fintype.card V := by
  classical
  letI : DecidableRel L.Adj := dL
  constructor
  · have hC : 0 < C.card := by
      obtain ⟨v⟩ := (Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V))
      obtain ⟨s, hs, _⟩ := hcover v
      exact Finset.card_pos.mpr ⟨s, hs⟩
    by_contra h
    have hle : C.card ≤ 1 := by omega
    have hone : C.card = 1 := by omega
    obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hone
    have hCs : C = {s} := hs
    have hfull : s = Finset.univ := by
      ext v
      constructor
      · intro _
        simp
      · intro _
        obtain ⟨t, ht, hvt⟩ := hcover v
        have hts : t = s := by simpa [hCs] using ht
        simpa [hts] using hvt
    have hL : L.Connected := by
      have hsc : s ∈ C := by rw [hCs]; simp
      have hc := hconnected s hsc
      have hsets : (↑s : Set V) = Set.univ := by
        ext v
        simp [hfull]
      rw [hsets] at hc
      exact L.induceUnivIso.connected_iff.mp hc
    exact hconn hL
  · have hd : (C : Set (Finset V)).PairwiseDisjoint (fun s => s) := by
      intro s hs t ht hst
      exact hdisjoint s hs t ht hst
    have hu : C.biUnion (fun s => s) = Finset.univ := by
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
      exact hcover v
    calc
      (∑ s ∈ C, s.card) = (C.biUnion (fun s => s)).card := by
        exact (Finset.card_biUnion hd).symm
      _ = Fintype.card V := by rw [hu]; simp