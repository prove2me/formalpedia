-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_extension_maximality__p2m_8122a02e_177a_44bd_9de8_e1e79416f7a3_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:26:05.222028+00:00
-- url     : https://prove2.me/submissions/f22b8e39-ba2d-4e3b-b93a-46fc05ce492b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P N)
    (hstep : ∀ M : SimpleGraph V, N ≤ M → P M → ¬ M.Connected →
      ∃ K : SimpleGraph V, M ≤ K ∧ P K ∧ M ≠ K) :
    ∃ M : SimpleGraph V, N ≤ M ∧ P M ∧ M.Connected := by
  classical
  let S : Set (SimpleGraph V) := {M | N ≤ M ∧ P M}
  have hSfinite : S.Finite := Set.finite_univ.subset (by
    intro M hM
    simp)
  have hSnonempty : S.Nonempty := ⟨N, by simp [S, hP]⟩
  obtain ⟨M, hM, hmax⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨M, hM.1, hM.2, ?_⟩
  by_contra hNotConnected
  obtain ⟨K, hMK, hPK, hne⟩ := hstep M hM.1 hM.2 hNotConnected
  have hK : K ∈ S := ⟨hM.1.trans hMK, hPK⟩
  have hKM : K ≤ M := hmax hK hMK
  exact hne (le_antisymm hMK hKM)