-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.positiveBlock_suffix_visits_target_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:00:58.213204+00:00
-- url     : https://prove2.me/submissions/e201384e-ecb6-4224-b8ab-f245214c3cb9

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Theorems.Thm_QEC_Distillation_PhaseRetry_visitsTarget_append_right
import Theorems.Thm_QEC_Distillation_PhaseRetry_positiveBlock_visits_target_eight

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution
    (start target : ZMod 8) (history : List Bool) :
    visitsTarget start target (history ++ positiveBlock 8) := by
  apply visitsTarget_append_right history (positiveBlock 8)
  exact positiveBlock_visits_target_eight (endpoint start history) target
end QEC.Distillation.PhaseRetry
