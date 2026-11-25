-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.SD.p_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:37:49.384558+00:00
-- url     : https://prove2.me/submissions/3234cdac-a49c-49a6-8f30-92839f948b31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_RingTopologyInstances
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitSplit
import Theorems.Thm_PI_LocDualGen_EpS_pr_f
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabSW_secondCountable_Fv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
open PI.UnitaryGroupMassFormula.LocJacTyp.SD
variable {σ v} (D : SD σ v)
namespace PI.UnitaryGroupMassFormula.LocJacTyp.SD
theorem _root_.solution : D.p 0 (1 - D.e) = 0 ∧ D.p 1 (1 - D.e) = 1 := PI.LocDualGen.EpS.pr_f D.hr D.e D.he D.h0 D.h1
end PI.UnitaryGroupMassFormula.LocJacTyp.SD
