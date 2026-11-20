-- Prove2me | solution 1 for QEC.Distillation.BK05T.tTwirl_canonicalizedInput_eq_diagonalInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:07:31.387958+00:00
-- url     : https://prove2.me/submissions/7e9d120a-e98f-42ac-bed5-e5c6417f8172

import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence
import Theorems.Thm_QEC_Distillation_BK05T_tTwirlChannel_mapDensity
import Theorems.Thm_QEC_Distillation_BK05T_tTwirlChannel_mapDensity_canonicalizedInput
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic

theorem _root_.solution
    (rho : DensityOperator QubitSpace) :
    tTwirl (tCanonicalizedInput rho) =
      tDiagonalInput (bk05TFidelityError rho)
        (bk05TFidelityError_nonneg rho) (bk05TFidelityError_le_one rho) := by
  simpa only [tTwirlChannel_mapDensity, bk05TFidelityError] using
    tTwirlChannel_mapDensity_canonicalizedInput rho
