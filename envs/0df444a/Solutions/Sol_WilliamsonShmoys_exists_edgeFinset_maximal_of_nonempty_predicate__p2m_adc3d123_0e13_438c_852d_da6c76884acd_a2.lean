-- Prove2me | solution 1 for WilliamsonShmoys.exists_edgeFinset_maximal_of_nonempty_predicate__p2m_adc3d123_0e13_438c_852d_da6c76884acd_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:11:43.833807+00:00
-- url     : https://prove2.me/submissions/d979a342-c9f5-49f7-b132-bedc204cc546

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (hP : ∃ G, P G) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    ∃ G : SimpleGraph V,
      P G ∧
      ∀ H : SimpleGraph V,
        G.edgeFinset ⊆ H.edgeFinset →
        P H →
        H.edgeFinset ⊆ G.edgeFinset := by
  classical
  letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
    fun G => Classical.decRel G.Adj
  let s : Finset (SimpleGraph V) := Finset.univ.filter P
  have hs : s.Nonempty := by
    obtain ⟨G, hG⟩ := hP
    exact ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ G, hG⟩⟩
  obtain ⟨G, hG, hmax⟩ :=
    Finset.exists_max_image s (fun G : SimpleGraph V => G.edgeFinset.card) hs
  refine ⟨G, (Finset.mem_filter.mp hG).2, ?_⟩
  intro H hsub hH
  have hHmem : H ∈ s := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ H, hH⟩
  have hcard : H.edgeFinset.card ≤ G.edgeFinset.card := hmax H hHmem
  have heq : G.edgeFinset = H.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub hcard
  simpa [heq]