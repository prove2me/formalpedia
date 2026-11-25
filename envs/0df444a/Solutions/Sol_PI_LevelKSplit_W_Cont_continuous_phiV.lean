-- Prove2me | solution 1 for PI.LevelKSplit.W.Cont.continuous_phiV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:10:23.699912+00:00
-- url     : https://prove2.me/submissions/d5a792cd-6b04-447f-9718-829473f126ee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousAtPlace
import Theorems.Thm_PI_LevelKSplit_W_Cont_continuous_evalV

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace PI.LevelKSplit.W.Cont
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) : Continuous (phiV (E := E) v) := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  have : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul (Fv F v) _
  exact IsModuleTopology.continuous_of_linearMapₛₗ (continuous_evalV v) (phiSL v)
end PI.LevelKSplit.W.Cont
