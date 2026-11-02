-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_extension_finite__p2m_0a2f9458_d7af_417f_8026_7751bf7a2ead_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:43:50.118561+00:00
-- url     : https://prove2.me/submissions/f62002f5-f4b0-4107-bb19-ebb5acbcd267

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (P : SimpleGraph V → Prop)
    (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (K : SimpleGraph V) (hK : P K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ P L ∧
      ∀ M : SimpleGraph V, L ≤ M → P M → M ≤ L := by
  classical
  let S : Set (SimpleGraph V) := {G | K ≤ G ∧ P G}
  have hSfinite : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨K, by simp [S, hK]⟩
  obtain ⟨L, hLmem, hLmax⟩ :=
    Set.exists_max_image S (fun G : SimpleGraph V => G.edgeFinset.card) hSfinite hSne
  have hL : K ≤ L ∧ P L := by simpa [S] using hLmem
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro M hLM hPM
  by_contra hML
  have hMLlt : L < M := lt_iff_le_not_ge.mpr ⟨hLM, hML⟩
  have hcardlt : L.edgeFinset.card < M.edgeFinset.card := by
    apply Finset.card_lt_card
    rw [SimpleGraph.edgeFinset_ssubset_edgeFinset]
    exact hMLlt
  have hMmem : M ∈ S := by
    simp [S, hL.1.trans hLM, hPM]
  have hcardle := hLmax M hMmem
  omega