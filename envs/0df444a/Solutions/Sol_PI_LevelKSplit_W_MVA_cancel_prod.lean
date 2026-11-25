-- Prove2me | solution 1 for PI.LevelKSplit.W.MVA.cancel_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:48:39.956474+00:00
-- url     : https://prove2.me/submissions/c41939bb-4264-4811-b638-2b8bf4e52bfa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MapFstConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousFirstOrbitMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.MVA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
namespace PI.LevelKSplit.W.MVA
theorem _root_.solution {X Y : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    (ν : Measure X) [ν.IsAddHaarMeasure] [SFinite ν] (a b : Measure Y) [SFinite a] [SFinite b]
    (h : ν.prod a = ν.prod b) : a = b := by
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : X)
  have h0 : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hKn).ne'
  have hinf : ν K ≠ ⊤ := hK.measure_lt_top.ne
  ext s hs
  have h1 := congrArg (fun m => m (K ×ˢ s)) h
  simp only [Measure.prod_prod] at h1
  exact (ENNReal.mul_right_inj h0 hinf).1 h1
end PI.LevelKSplit.W.MVA
