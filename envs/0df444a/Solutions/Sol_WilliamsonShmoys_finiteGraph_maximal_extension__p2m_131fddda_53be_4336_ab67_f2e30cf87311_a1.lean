-- Prove2me | solution 1 for WilliamsonShmoys.finiteGraph_maximal_extension__p2m_131fddda_53be_4336_ab67_f2e30cf87311_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:56:18.265457+00:00
-- url     : https://prove2.me/submissions/c7d2afd8-2a42-4fcb-a6ae-af2cabeb5860

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (L : SimpleGraph V) (P : SimpleGraph V → Prop) (hL : P L) : ∃ M : SimpleGraph V, LE.le L M ∧ P M ∧ ∀ N : SimpleGraph V, LE.le M N → P N → N = M := by
  classical
  let Q : SimpleGraph V → Prop := fun G => L ≤ G ∧ P G
  obtain ⟨M, hLM, hMmax⟩ :=
    Finite.exists_le_maximal (a := L) (p := Q) ⟨le_rfl, hL⟩
  refine ⟨M, hLM, hMmax.1.2, ?_⟩
  intro N hMN hPN
  have hQN : Q N := ⟨hLM.trans hMN, hPN⟩
  exact le_antisymm (hMmax.2 hQN hMN) hMN