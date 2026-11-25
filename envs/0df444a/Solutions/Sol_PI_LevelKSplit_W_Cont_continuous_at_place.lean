-- Prove2me | solution 1 for PI.LevelKSplit.W.Cont.continuous_at_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:18:10.973915+00:00
-- url     : https://prove2.me/submissions/975a65c6-752d-4a1c-98aa-a8f8f9b4db86

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousAtPlace
import Theorems.Thm_PI_LevelKSplit_W_Cont_continuous_phiV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Cont
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
namespace PI.LevelKSplit.W.Cont
theorem _root_.solution : PI.LevelKSplit.W.Meas.ContPlace := by
  intro F E _ _ _ _ _ σ n J v
  have h1 : Continuous (fun g : HA (Af F) σ J => (incAf σ J g : GL (Fin n) (Af F ⊗[F] E))) :=
    continuous_subtype_val
  have h2 : Continuous (fun g : HA (Af F) σ J =>
      ((incAf σ J g : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))) :=
    Units.continuous_val.comp h1
  refine (h2.matrix_map (continuous_phiV (E := E) v)).congr ?_
  intro g
  rfl
end PI.LevelKSplit.W.Cont
