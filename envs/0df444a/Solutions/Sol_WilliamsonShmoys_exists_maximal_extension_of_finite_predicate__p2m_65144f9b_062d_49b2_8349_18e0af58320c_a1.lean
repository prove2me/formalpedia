-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_extension_of_finite_predicate__p2m_65144f9b_062d_49b2_8349_18e0af58320c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:41:07.880224+00:00
-- url     : https://prove2.me/submissions/9c9f461e-8866-44c5-9ce0-b1600605aecf

import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_mem_of_finite_poset__p2m_060318e6_9aa2_44ce_a8eb_f04f288fc5e7_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hL : P L)
    (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G) :
    ∃ T : SimpleGraph V,
      L ≤ T ∧ P T ∧
        ∀ U : SimpleGraph V, T ≤ U → P U → U ≤ T := by
  classical
  let s : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => L ≤ G ∧ P G)
  have hs : s.Nonempty := by
    refine ⟨L, ?_⟩
    simp [s, hL]
  obtain ⟨T, hT, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_mem_of_finite_poset__p2m_060318e6_9aa2_44ce_a8eb_f04f288fc5e7_a2 s hs
  refine ⟨T, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hT).2.1
  · exact (Finset.mem_filter.mp hT).2.2
  · intro U hTU hPU
    apply hmax U
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨le_trans (Finset.mem_filter.mp hT).2.1 hTU, hPU⟩⟩
    · exact hTU
