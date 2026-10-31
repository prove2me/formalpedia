-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_extension_maximal__p2m_624a938d_c9e5_41fb_88c5_28ffcc896cfe_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:47:59.474914+00:00
-- url     : https://prove2.me/submissions/5411ef99-dc6e-4e55-9aa2-e10cb3581478

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (H : SimpleGraph V)
    (P : SimpleGraph V → Prop) (hP : P H) :
    ∃ T : SimpleGraph V, H ≤ T ∧ P T ∧
      ∀ U : SimpleGraph V, T ≤ U → P U → U = T := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun T => H ≤ T ∧ P T
  have hS : S.Nonempty := by
    refine ⟨H, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, le_rfl, hP⟩
  obtain ⟨T, hT, hmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeFinset.card) hS
  have hTmem := Finset.mem_filter.mp hT
  refine ⟨T, hTmem.2.1, hTmem.2.2, ?_⟩
  intro U hTU hPU
  have hU : U ∈ S := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, le_trans hTmem.2.1 hTU, hPU⟩
  by_contra hne
  have hlt : T < U := lt_of_le_of_ne hTU (Ne.symm hne)
  have hcard : T.edgeFinset.card < U.edgeFinset.card :=
    Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hlt)
  exact (not_lt_of_ge (hmax U hU)) hcard