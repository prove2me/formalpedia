-- Prove2me | solution 1 for P7ThreeColor.Lemma11.X_no_nbr_in_S
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:28:42.721547+00:00
-- url     : https://prove2.me/submissions/31669c18-c9f9-4eee-a482-559178c2594c

import Mathlib
import Definitions.Def_P7ThreeColor_Lemma11_Setting

set_option autoImplicit false
open P7ThreeColor.Lemma11

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (L : V → Finset (Fin 3)) (S : Finset V) (hyp : Lemma11Hyp G L S)
    (x s : V) (hx : x ∈ X L) (hs : s ∈ S) :
    ¬ G.Adj x s := by
  intro hadj
  have hx3 : (L x).card = 3 := by simpa [X] using hx
  by_cases hxS : x ∈ S
  · have := hyp.seed.card_S x hxS
    omega
  · have hn : x ∈ P7ThreeColor.Seed.nbhd G S := by
      simp only [P7ThreeColor.Seed.nbhd, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hxS, s, hs, hadj⟩
    have := hyp.seed.card_N x hn
    omega
