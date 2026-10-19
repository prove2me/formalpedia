-- Prove2me | solution 1 for QAlgorithms.Childs.bipartite_local_edgeColouring
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:30:36.774348+00:00
-- url     : https://prove2.me/submissions/5ffafa27-517d-45f7-afd9-bc115ae2cd30

import Definitions.Def_QAlgorithms_Defs_Walk

open QAlgorithms

private def localColour {N : ℕ}
    (a b : Fin N × Bool × List (Fin N)) : ℕ × ℕ :=
  if a.2.1 then (a.2.2.idxOf b.1, b.2.2.idxOf a.1)
  else (b.2.2.idxOf a.1, a.2.2.idxOf b.1)

theorem solution (N d : ℕ) :
    ∃ rule : Fin N × Bool × List (Fin N) → Fin N × Bool × List (Fin N) → ℕ × ℕ,
      ∀ (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (side : Fin N → Bool),
        IsBipartition G side → G.maxDegree ≤ d →
        ∀ nbr : Fin N → List (Fin N), IsNeighbourList G nbr →
          IsProperEdgeColouring G (fun u v => rule (u, side u, nbr u) (v, side v, nbr v)) ∧
          ((Finset.univ.filter fun p : Fin N × Fin N => G.Adj p.1 p.2).image
              fun p => rule (p.1, side p.1, nbr p.1) (p.2, side p.2, nbr p.2)).card ≤ d ^ 2 := by
  classical
  refine ⟨localColour, ?_⟩
  intro G _ side hside hdegree nbr hnbr
  have hlen (u : Fin N) : (nbr u).length ≤ d := by
    have heq : (nbr u).toFinset = G.neighborFinset u := by
      ext v
      simp only [List.mem_toFinset, SimpleGraph.mem_neighborFinset]
      exact (hnbr u).2 v
    have hcard : (nbr u).toFinset.card = (nbr u).length :=
      List.toFinset_card_of_nodup (hnbr u).1
    rw [heq, G.card_neighborFinset_eq_degree] at hcard
    exact hcard ▸ (G.degree_le_maxDegree u).trans hdegree
  have hidx (u v : Fin N) (h : G.Adj u v) : (nbr u).idxOf v < d :=
    (List.idxOf_lt_length_of_mem ((hnbr u).2 v |>.mpr h)).trans_le (hlen u)
  constructor
  · constructor
    · intro u v huv
      have hs := hside u v huv
      cases hu : side u <;> cases hv : side v <;>
        simp_all [localColour]
    · intro u v w huv huw hvw heq
      apply hvw
      apply (List.idxOf_inj ((hnbr u).2 v |>.mpr huv)).mp
      cases hu : side u
      · simpa [localColour, hu] using congrArg Prod.snd heq
      · simpa [localColour, hu] using congrArg Prod.fst heq
  · have hsub :
        ((Finset.univ.filter fun p : Fin N × Fin N => G.Adj p.1 p.2).image
          fun p => localColour (p.1, side p.1, nbr p.1) (p.2, side p.2, nbr p.2)) ⊆
            (Finset.range d) ×ˢ (Finset.range d) := by
      intro c hc
      obtain ⟨⟨u,v⟩, hmem, rfl⟩ := Finset.mem_image.mp hc
      have huv : G.Adj u v := (Finset.mem_filter.mp hmem).2
      have h₁ := hidx u v huv
      have h₂ := hidx v u huv.symm
      cases side u <;> simp [localColour, h₁, h₂]
    calc
      _ ≤ ((Finset.range d) ×ˢ (Finset.range d)).card := Finset.card_le_card hsub
      _ = d ^ 2 := by simp [pow_two]
