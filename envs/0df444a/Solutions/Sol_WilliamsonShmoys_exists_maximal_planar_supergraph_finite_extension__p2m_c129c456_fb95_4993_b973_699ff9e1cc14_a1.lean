-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_finite_extension__p2m_c129c456_fb95_4993_b973_699ff9e1cc14_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:29:28.48977+00:00
-- url     : https://prove2.me/submissions/ca1ce2d1-7bb9-42a1-9ed4-008bcc692d5d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (P : SimpleGraph V → Prop) (hP : P H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      P K ∧
      (∀ L : SimpleGraph V, K ≤ L → P L → L ≤ K) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  classical
  let S : Set (SimpleGraph V) := {K | H ≤ K ∧ P K}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨H, le_rfl, hP⟩
  obtain ⟨K, hKmax⟩ := hSfinite.exists_maximal hSnonempty
  rcases hKmax with ⟨hKS, hKmax⟩
  change H ≤ K ∧ P K at hKS
  refine ⟨K, hKS.1, hKS.2, ?_, ?_⟩
  · intro L hKL hPL
    apply hKmax
    · exact ⟨hKS.1.trans hKL, hPL⟩
    · exact hKL
  · exact Set.ncard_mono (SimpleGraph.edgeSet_mono hKS.1)