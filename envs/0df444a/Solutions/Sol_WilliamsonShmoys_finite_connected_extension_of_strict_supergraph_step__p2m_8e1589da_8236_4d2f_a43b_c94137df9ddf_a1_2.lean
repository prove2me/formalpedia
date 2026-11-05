-- Prove2me | solution 2 for WilliamsonShmoys.finite_connected_extension_of_strict_supergraph_step__p2m_8e1589da_8236_4d2f_a43b_c94137df9ddf_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:20:32.347501+00:00
-- url     : https://prove2.me/submissions/b19d3e98-27b1-458f-8347-1ad2f69cff38

import Mathlib

set_option linter.unusedVariables false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P G)
    (hstep : ∀ H : SimpleGraph V, G ≤ H → P H → ¬ H.Connected →
      ∃ H' : SimpleGraph V, H < H' ∧ P H') :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ P H := by
  classical
  let p : SimpleGraph V → Prop := fun H => G ≤ H ∧ P H
  have hpG : p G := ⟨le_rfl, hP⟩
  obtain ⟨H, hGH, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := G) hpG)
  rcases hmax with ⟨hpH, hmax'⟩
  by_cases hc : H.Connected
  · exact ⟨H, hpH.1, hc, hpH.2⟩
  · exfalso
    obtain ⟨H', hHH', hPH'⟩ := hstep H hpH.1 hpH.2 hc
    have hp' : p H' := ⟨hpH.1.trans (le_of_lt hHH'), hPH'⟩
    have hH'H : H' ≤ H := hmax' hp' (le_of_lt hHH')
    exact (lt_irrefl H) (lt_of_lt_of_le hHH' hH'H)
