-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_completion_maximal_extension__p2m_7f97800d_a064_49bc_abdc_383c926e2440_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:28:58.870409+00:00
-- url     : https://prove2.me/submissions/711f9b51-e8ef-4382-ad52-4adfc416694b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L) : exists M : SimpleGraph V, LE.le L M /\ WilliamsonShmoys.HasPlanarDrawingOn M /\ forall N : SimpleGraph V, LE.le M N -> WilliamsonShmoys.HasPlanarDrawingOn N -> N = M := by
  classical
  let p : SimpleGraph V -> Prop := fun M => LE.le L M /\ WilliamsonShmoys.HasPlanarDrawingOn M
  have hL : p L := ⟨le_rfl, hLplanar⟩
  obtain ⟨M, hLM, hMmax⟩ := Finite.exists_le_maximal hL
  refine ⟨M, hLM, hMmax.prop.2, ?_⟩
  intro N hMN hNplanar
  have hN : p N := ⟨hLM.trans hMN, hNplanar⟩
  exact hMmax.eq_of_ge hN hMN