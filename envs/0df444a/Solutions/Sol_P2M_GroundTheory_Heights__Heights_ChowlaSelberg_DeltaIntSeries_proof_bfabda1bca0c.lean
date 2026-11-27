-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaIntSeries_proof_bfabda1bca0c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:53:08.359424+00:00
-- url     : https://prove2.me/submissions/62f17821-6b87-4a24-b8fb-db2ca734c47b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_DeltaIntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PDeltaIntSeries
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_pow_36e45add25b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesEval_pow_1a9d7efbc52a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_pentagonalSeries_bdc5530baf37
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_tprod_one_sub_pow_eq_intSeriesEval_f6fd74baf778

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ChowlaSelberg
open PowerSeries Filter Topology Finset
open scoped Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg
namespace DeltaIntSeries
theorem _root_.solution : DeltaIntSeries.Statement := by
  refine ⟨pentagonalSeries ℤ ^ 24, ?_, fun r hr hr1 ↦
    intSeriesConv_pow hr (intSeriesConv_pentagonalSeries hr hr1) 24, fun τ ↦ ?_⟩
  · have h0 : coeff 0 (pentagonalSeries ℤ) = 1 := by
      have h := coeff_pentagonalSeries_pentagonal ℤ 0
      rwa [show pentagonal 0 = 0 by simp [pentagonal_def], Int.negOnePow_zero, Units.val_one] at h
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, ← coeff_zero_eq_constantCoeff_apply, h0,
      one_pow]
  · have hq : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 := by
      simpa using τ.norm_qParam_lt_one 1
    rw [ModularForm.discriminant_eq_q_prod]
    simp only [ModularForm.eta_q]
    rw [(ModularForm.multipliable_one_sub_pow hq).tprod_pow,
      tprod_one_sub_pow_eq_intSeriesEval hq,
      intSeriesEval_pow (intSeriesConv_pentagonalSeries (norm_nonneg _) hq)]
end DeltaIntSeries
end GroundTheory.Heights₂.Heights.ChowlaSelberg
