-- Prove2me | solution 1 for SupplyChainTheory.handshaking
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T20:30:57.554714+00:00
-- url     : https://prove2.me/submissions/acf11c4f-2560-41a0-87f0-92b117b17d68

import Mathlib
import Definitions.Def_SupplyChainTheory_tsp

open Classical

theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Even (Finset.univ.filter (fun v => Odd (G.degree v))).card := by
  classical
  convert G.even_card_odd_degree_vertices
