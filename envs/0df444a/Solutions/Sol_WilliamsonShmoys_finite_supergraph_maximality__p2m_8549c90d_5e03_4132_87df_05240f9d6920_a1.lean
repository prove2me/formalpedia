-- Prove2me | solution 1 for WilliamsonShmoys.finite_supergraph_maximality__p2m_8549c90d_5e03_4132_87df_05240f9d6920_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:58:31.73628+00:00
-- url     : https://prove2.me/submissions/5bba57a2-ba74-46ed-803e-f15b24cca2b4

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (P : SimpleGraph V → Prop)
    (H : SimpleGraph V) (hH : P H) :
    ∃ J : SimpleGraph V, H ≤ J ∧ P J ∧
      (∀ K : SimpleGraph V, J ≤ K → P K → K ≤ J) := by
  classical
  let S : Set (SimpleGraph V) := {J | H ≤ J ∧ P J}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨H, le_rfl, hH⟩
  obtain ⟨J, hJmax⟩ := hSfinite.exists_maximal hSnonempty
  rcases hJmax with ⟨hJmem, hJmax⟩
  rcases hJmem with ⟨hHJ, hPJ⟩
  refine ⟨J, hHJ, hPJ, ?_⟩
  intro K hJK hPK
  have hKmem : K ∈ S := ⟨hHJ.trans hJK, hPK⟩
  exact hJmax hKmem hJK