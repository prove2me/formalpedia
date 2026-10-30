-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_finite_saturation__p2m_db8af417_0538_4cad_8510_71b3310eaec4_a3
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T06:30:49.974983+00:00
-- url     : https://prove2.me/submissions/c9a96f73-839f-4342-aba3-5069f42f8350

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (hStep : ∀ G : SimpleGraph V, P G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧ H ≠ G)
    (G : SimpleGraph V)
    (hG : P G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ P H ∧ H.Connected ∧
      (G.edgeSet.ncard : Int) ≤ (H.edgeSet.ncard : Int) := by
  classical
  have hmono : ∀ A B : SimpleGraph V, A ≤ B → A.edgeSet.ncard ≤ B.edgeSet.ncard := by
    intro A B hAB
    apply Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hAB) (Set.toFinite _)
  have hfin : {H : SimpleGraph V | G ≤ H ∧ P H}.Finite := Set.toFinite _
  obtain ⟨H, hHm, hmax⟩ := Finset.exists_max_image hfin.toFinset
    (fun H => H.edgeSet.ncard) ⟨G, by simpa using And.intro (le_refl G) hG⟩
  have hHm' : G ≤ H ∧ P H := by simpa using hHm
  have hmax' : ∀ H' : SimpleGraph V, G ≤ H' ∧ P H' → H'.edgeSet.ncard ≤ H.edgeSet.ncard :=
    fun H' h => hmax H' (by simpa using h)
  obtain ⟨hGH, hPH⟩ := hHm'
  refine ⟨H, hGH, hPH, ?_, ?_⟩
  · by_contra hnc
    obtain ⟨H', hHH', hP', hne⟩ := hStep H hPH hnc
    have h1 := hmax' H' ⟨hGH.trans hHH', hP'⟩
    have h2 : H.edgeSet.ncard < H'.edgeSet.ncard := by
      apply Set.ncard_lt_ncard _ (Set.toFinite _)
      refine lt_of_le_of_ne (SimpleGraph.edgeSet_mono hHH') ?_
      intro heq
      apply hne
      apply le_antisymm
      · exact fun u v h => by
          have : s(u, v) ∈ H'.edgeSet := h
          rw [← heq] at this
          exact this
      · exact hHH'
    omega
  · exact_mod_cast hmono _ _ hGH
