-- Prove2me | solution 1 for P7ThreeColor.Lemma11.list_of_seed_nbr
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:28:43.655931+00:00
-- url     : https://prove2.me/submissions/bc9bb4ba-e26a-48c1-b8bb-8e3463faa343

import Mathlib
import Definitions.Def_P7ThreeColor_Lemma11_Setting

set_option autoImplicit false
open P7ThreeColor.Lemma11

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (L : V → Finset (Fin 3)) (S : Finset V) (hyp : Lemma11Hyp G L S)
    (i : Fin 3) (d s : V) (hd : d ∈ D G L S i) (hs : s ∈ S) (hds : G.Adj d s) :
    L s = {i} := by
  unfold D at hd
  rw [Finset.mem_filter] at hd
  obtain ⟨hdn, hLd⟩ := hd
  have hdis := hyp.noShare s hs d hdn hds.symm
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hyp.seed.card_S s hs)
  rw [ha, hLd, Finset.disjoint_singleton_left] at hdis
  rw [ha]
  by_contra hne
  apply hdis
  have : a ≠ i := fun h => hne (by rw [h])
  simp [this]
