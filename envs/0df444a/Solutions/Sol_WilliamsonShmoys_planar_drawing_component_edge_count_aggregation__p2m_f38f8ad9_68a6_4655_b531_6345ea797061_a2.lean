-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_component_edge_count_aggregation__p2m_f38f8ad9_68a6_4655_b531_6345ea797061_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T21:04:24.792017+00:00
-- url     : https://prove2.me/submissions/3103194e-3637-4ac3-a697-f5a1ff8bb2a6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj] (hV : 3 ≤ Fintype.card V)
    (hconnected : ∀ {W : Type} [Fintype W] [LinearOrder W]
      (G : SimpleGraph W) (hW : 3 ≤ Fintype.card W)
      (hconn : G.Connected) (hG : HasPlanarDrawingOn G),
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj
       G.edgeFinset.card + 6 ≤ 3 * Fintype.card W))
    (C : Finset (Finset V))
    (hpos : ∀ B ∈ C, 0 < B.card)
    (hdisj : ∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ≠ B₂ →
      Disjoint (↑B₁ : Set V) (↑B₂ : Set V))
    (hcover : ∀ v : V, ∃ B ∈ C, v ∈ B)
    (hcard : Fintype.card V = ∑ B ∈ C, B.card)
    (hbig : ∀ B ∈ C, 3 ≤ B.card →
      letI : DecidableRel N.Adj := Classical.decRel N.Adj
      letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
      (N.induce (↑B : Set V)).Connected ∧
      HasPlanarDrawingOn (N.induce (↑B : Set V)))
    (hsingle : ∀ B ∈ C, B.card = 1 →
      letI : DecidableRel N.Adj := Classical.decRel N.Adj
      letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
      (N.induce (↑B : Set V)).edgeFinset.card = 0)
    (hpair : ∀ B ∈ C, B.card = 2 →
      letI : DecidableRel N.Adj := Classical.decRel N.Adj
      letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
      (N.induce (↑B : Set V)).edgeFinset.card ≤ 1)
    (hedge : N.edgeFinset.card =
      ∑ B ∈ C, (letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _;
        (N.induce (↑B : Set V)).edgeFinset.card)) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     N.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  let e : Finset V → Nat := fun B =>
    letI : DecidableRel N.Adj := Classical.decRel N.Adj
    letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
    (N.induce (↑B : Set V)).edgeFinset.card
  have hcardSubtype (B : Finset V) :
      Fintype.card {v // v ∈ (↑B : Set V)} = B.card := by
    simpa using Fintype.card_coe (↑B : Set V)
  have hlocal : ∀ B ∈ C, e B ≤ 3 * B.card ∧
      (3 ≤ B.card → e B + 6 ≤ 3 * B.card) := by
    intro B hB
    have hn := hpos B hB
    by_cases hlarge : 3 ≤ B.card
    · letI : DecidableRel N.Adj := Classical.decRel N.Adj
      letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
      let G := N.induce (↑B : Set V)
      letI : DecidableRel G.Adj := Classical.decRel G.Adj
      have hG := hbig B hB hlarge
      have hbound := hconnected G (by simpa [G, hcardSubtype] using hlarge)
        hG.1 hG.2
      have hEdgeCount : G.edgeFinset.card = e B := by
        dsimp [e, G]
        congr 1
      have hstrong : e B + 6 ≤ 3 * B.card := by
        calc
          e B + 6 = G.edgeFinset.card + 6 := by rw [hEdgeCount]
          _ ≤ 3 * B.card := by simpa [hcardSubtype] using hbound
      exact ⟨by omega, fun _ => hstrong⟩
    · by_cases hone : B.card = 1
      · have he := hsingle B hB hone
        have he' : e B = 0 := by simpa [e] using he
        constructor <;> omega
      · have htwo : B.card = 2 := by omega
        have he := hpair B hB htwo
        have he' : e B ≤ 1 := by simpa [e] using he
        constructor <;> omega
  have hNedge :
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj; N.edgeFinset.card) =
        N.edgeFinset.card := by
    congr 1
    ext x
    simp [SimpleGraph.mem_edgeFinset]
  have hedge' :
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj; N.edgeFinset.card) =
        ∑ B ∈ C, e B := by
    rw [hNedge, hedge]
    apply Finset.sum_congr rfl
    intro B hB
    dsimp [e]
    congr 1
    ext x
    simp [SimpleGraph.mem_edgeFinset]
  by_cases hex : ∃ B ∈ C, 3 ≤ B.card
  · obtain ⟨b, hbC, hbsize⟩ := hex
    have hpoint : ∀ B ∈ C,
        e B + (if B = b then 6 else 0) ≤ 3 * B.card := by
      intro B hB
      by_cases hEq : B = b
      · subst B
        have hs := (hlocal b hbC).2 hbsize
        simpa using hs
      · have hs := (hlocal B hB).1
        simp [hEq]
        omega
    have hsum := Finset.sum_le_sum hpoint
    have hsumIf : (∑ B ∈ C, if B = b then 6 else 0) = 6 := by
      rw [Finset.sum_eq_single b]
      · simp
      · intro x hx hxb
        simp [hxb]
      · intro hbnot
        exact False.elim (hbnot hbC)
    rw [Finset.sum_add_distrib, hsumIf] at hsum
    have hsum3 : (∑ B ∈ C, 3 * B.card) = 3 * (∑ B ∈ C, B.card) := by
      simp [Finset.mul_sum]
    rw [hsum3] at hsum
    calc
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj; N.edgeFinset.card) + 6
          = (∑ B ∈ C, e B) + 6 := by rw [hedge']
      _ ≤ 3 * (∑ B ∈ C, B.card) := hsum
      _ = 3 * Fintype.card V := by rw [← hcard]
  · have hsmall : ∀ B ∈ C, e B ≤ B.card := by
      intro B hB
      have hn := hpos B hB
      by_cases hone : B.card = 1
      · have he := hsingle B hB hone
        have he' : e B = 0 := by simpa [e] using he
        omega
      · have htwo : B.card = 2 := by
          have hnotlarge : ¬ 3 ≤ B.card := by
            intro hlarge
            exact hex ⟨B, hB, hlarge⟩
          omega
        have he := hpair B hB htwo
        have he' : e B ≤ 1 := by simpa [e] using he
        omega
    have hsumSmall := Finset.sum_le_sum hsmall
    have htotal : 3 ≤ ∑ B ∈ C, B.card := by simpa [hcard] using hV
    have hfinal : (∑ B ∈ C, e B) + 6 ≤ 3 * (∑ B ∈ C, B.card) := by omega
    calc
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj; N.edgeFinset.card) + 6
          = (∑ B ∈ C, e B) + 6 := by rw [hedge']
      _ ≤ 3 * (∑ B ∈ C, B.card) := hfinal
      _ = 3 * Fintype.card V := by rw [← hcard]
