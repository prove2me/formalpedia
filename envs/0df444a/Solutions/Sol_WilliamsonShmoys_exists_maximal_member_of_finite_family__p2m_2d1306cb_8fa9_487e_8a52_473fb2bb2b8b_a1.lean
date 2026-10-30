-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_member_of_finite_family__p2m_2d1306cb_8fa9_487e_8a52_473fb2bb2b8b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:52:46.132067+00:00
-- url     : https://prove2.me/submissions/fb0e83bf-28a7-46df-89d5-5486e6275ced

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P H) :
    ∃ L : SimpleGraph V,
      H ≤ L ∧ P L ∧
      ∀ M : SimpleGraph V, L ≤ M → P M → M ≤ L := by
  classical
  let S : Set (SimpleGraph V) := {G | H ≤ G ∧ P G}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨H, le_rfl, hP⟩
  obtain ⟨L, hL⟩ := hSfinite.exists_maximal hSnonempty
  rcases hL with ⟨hLS, hLmax⟩
  refine ⟨L, hLS.1, hLS.2, ?_⟩
  intro M hLM hPM
  have hMS : M ∈ S := ⟨hLS.1.trans hLM, hPM⟩
  exact hLmax hMS hLM