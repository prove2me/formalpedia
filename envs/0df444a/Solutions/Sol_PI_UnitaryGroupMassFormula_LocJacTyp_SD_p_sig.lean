-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.SD.p_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:03:51.546812+00:00
-- url     : https://prove2.me/submissions/d5d9f978-eb8a-446d-89c9-ca3acc2f3f12

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_RingTopologyInstances
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitSplit
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_SD_decomp
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_SD_p_pair
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_sigR_smul
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
theorem _root_.solution (z : Fv F v ⊗[F] E) :
    D.p 0 (sigR (Fv F v) σ z) = D.p 1 z ∧ D.p 1 (sigR (Fv F v) σ z) = D.p 0 z := by
  have h : sigR (Fv F v) σ z = D.p 1 z • D.e + D.p 0 z • (1 - D.e) := by
    conv_lhs => rw [D.decomp z]
    rw [map_add, sigR_smul, sigR_smul, map_sub, map_one, D.hσ, sub_sub_cancel, add_comm]
  rw [h]
  exact D.p_pair _ _
end PI.UnitaryGroupMassFormula.LocJacTyp.SD
