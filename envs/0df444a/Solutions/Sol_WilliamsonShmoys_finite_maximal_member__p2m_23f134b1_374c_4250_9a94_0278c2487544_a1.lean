-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_member__p2m_23f134b1_374c_4250_9a94_0278c2487544_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:47:45.046029+00:00
-- url     : https://prove2.me/submissions/f5dc8854-bce4-4a4e-b885-4219e68da802

import Mathlib
set_option autoImplicit false

theorem solution {α : Type} [Fintype α] [PartialOrder α] (P : α → Prop) (s : α)
    (hP : P s) : ∃ m : α, s ≤ m ∧ P m ∧ ∀ b : α, m ≤ b → P b → b = m := by
  obtain ⟨m, hsm, hm⟩ := Finite.exists_le_maximal (p := P) hP
  refine ⟨m, hsm, hm.1, ?_⟩
  intro b hmb hPb
  exact le_antisymm (hm.2 hPb hmb) hmb