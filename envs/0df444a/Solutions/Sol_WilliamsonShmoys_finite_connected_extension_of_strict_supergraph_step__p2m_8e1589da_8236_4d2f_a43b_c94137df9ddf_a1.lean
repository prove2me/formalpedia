-- Prove2me | solution 1 for WilliamsonShmoys.finite_connected_extension_of_strict_supergraph_step__p2m_8e1589da_8236_4d2f_a43b_c94137df9ddf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:05:57.877812+00:00
-- url     : https://prove2.me/submissions/a784bcf9-2bcf-430c-8cbf-1fa19d13899d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_qualifying_supergraph__p2m_7b028f0e_9557_4d63_b320_a3debd61f7f1_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P G)
    (hstep : ∀ H : SimpleGraph V, G ≤ H → P H → ¬ H.Connected →
      ∃ H' : SimpleGraph V, H < H' ∧ P H') :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ P H := by
  obtain ⟨H, hGH, hPH, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_qualifying_supergraph__p2m_7b028f0e_9557_4d63_b320_a3debd61f7f1_a1
      G P hP
  by_contra hNoConnected
  have hNotConnected : ¬ H.Connected := by
    intro hConnected
    exact hNoConnected ⟨H, hGH, hConnected, hPH⟩
  obtain ⟨H', hStrict, hP'⟩ := hstep H hGH hPH hNotConnected
  exact hmax H' (le_trans hGH hStrict.le) hP' hStrict