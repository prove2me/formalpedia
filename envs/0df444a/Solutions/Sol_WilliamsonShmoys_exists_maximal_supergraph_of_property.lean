-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_property
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:25:15.650784+00:00
-- url     : https://prove2.me/submissions/fd29425a-fe73-4878-b69b-be92ccec1682

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (M : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      P N ∧
      ∀ K : SimpleGraph V, N ≤ K → P K → K = N := by
  classical
  let S : Set (SimpleGraph V) := {G | M ≤ G ∧ P G}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨M, le_rfl, hP⟩
  obtain ⟨N, hN⟩ := hSfinite.exists_maximal hSnonempty
  have hNmem : N ∈ S := hN.1
  refine ⟨N, hNmem.1, hNmem.2, ?_⟩
  intro K hNK hPK
  have hKN : K ≤ N := hN.2 ⟨hNmem.1.trans hNK, hPK⟩ hNK
  exact le_antisymm hKN hNK