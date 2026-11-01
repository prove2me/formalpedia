-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_extension_of_finite_predicate__p2m_c3e4c921_775b_4afc_815f_a590e3d69c46_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:05:00.664168+00:00
-- url     : https://prove2.me/submissions/a8b00ee4-7139-4dd7-a2e6-8fac24c7bbed

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (M : SimpleGraph V) (hM : P M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ P N ∧
      ∀ K : SimpleGraph V, N ≤ K → P K → K = N := by
  classical
  let S : Set (SimpleGraph V) := {G | M ≤ G ∧ P G}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨M, by simp [S, hM]⟩
  obtain ⟨N, hNS, hmax⟩ :=
    Set.exists_max_image S (fun G : SimpleGraph V => G.edgeFinset.card) hSfinite hSnonempty
  change M ≤ N ∧ P N at hNS
  refine ⟨N, hNS.1, hNS.2, ?_⟩
  intro K hNK hPK
  by_contra hKN
  have hneq : N ≠ K := fun h => hKN h.symm
  have hlt : N < K := lt_of_le_of_ne hNK hneq
  have hss : N.edgeFinset ⊂ K.edgeFinset :=
    SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt
  have hcard : N.edgeFinset.card < K.edgeFinset.card := Finset.card_lt_card hss
  have hMK : M ≤ K := le_trans hNS.1 hNK
  have hmaxK : K.edgeFinset.card ≤ N.edgeFinset.card := hmax K ⟨hMK, hPK⟩
  exact (Nat.not_lt_of_ge hmaxK) hcard
