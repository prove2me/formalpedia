-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_property_supergraph__p2m_8cd0804a_f792_4057_bb92_319536b24856_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:44:26.523918+00:00
-- url     : https://prove2.me/submissions/89f28445-0e36-4768-8871-297588d5e878

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ P M ∧
        ∀ N : SimpleGraph V, M ≤ N → P N → N ≤ M := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun H => G ≤ H ∧ P H)
  have hGmem : G ∈ S := by
    simp [S, hG]
  obtain ⟨M, hMmem, hMmax⟩ :=
    Finset.exists_max_image S (fun H => Fintype.card H.edgeSet) ⟨G, hGmem⟩
  have hMG : G ≤ M := by
    exact (Finset.mem_filter.mp hMmem).2.1
  have hPM : P M := (Finset.mem_filter.mp hMmem).2.2
  refine ⟨M, hMG, hPM, ?_⟩
  intro N hMN hPN
  have hNmem : N ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨le_trans hMG hMN, hPN⟩
  have hmax : Fintype.card N.edgeSet ≤ Fintype.card M.edgeSet :=
    hMmax N hNmem
  by_contra hNM
  have hlt : M < N := lt_iff_le_not_ge.mpr ⟨hMN, hNM⟩
  have hstrict : M.edgeSet ⊂ N.edgeSet :=
    SimpleGraph.edgeSet_ssubset_edgeSet.mpr hlt
  have hsub : M.edgeSet ⊆ N.edgeSet := hstrict.1
  let f : M.edgeSet → N.edgeSet := fun e => ⟨e.1, hsub e.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    change (⟨a.1, hsub a.2⟩ : N.edgeSet) = ⟨b.1, hsub b.2⟩ at hab
    have hv : a.1 = b.1 := congrArg (fun x : N.edgeSet => x.1) hab
    exact Subtype.ext hv
  have hns : ¬ Function.Surjective f := by
    intro hs
    obtain ⟨e, heN, heM⟩ := Set.not_subset.mp hstrict.2
    obtain ⟨d, hd⟩ := hs ⟨e, heN⟩
    have hde : d.1 = e := by
      simpa [f] using congrArg (fun x : N.edgeSet => x.1) hd
    exact heM (hde ▸ d.2)
  have hcardlt : Fintype.card M.edgeSet < Fintype.card N.edgeSet :=
    Fintype.card_lt_of_injective_not_surjective f hf hns
  omega