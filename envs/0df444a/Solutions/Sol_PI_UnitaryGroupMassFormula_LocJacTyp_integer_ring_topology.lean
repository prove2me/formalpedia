-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.integer_ring_topology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:57.059957+00:00
-- url     : https://prove2.me/submissions/618a10fb-863d-46c9-8941-f8be9da4f2ba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousTrESymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_RingTopologyInstances
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_oev_one
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_sc_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_oev_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_oev_sigR
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_isCompact_oev
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_isOpen_oev
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_oev_smul
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
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution : OTop (E := E) v :=
  ⟨Sd.isCompact_oev v, Sd.isOpen_oev v, oev_one v, fun _ hx _ hy => oev_mul v hx hy,
    fun _ hx _ hy => Sd.oev_add v hx hy, fun _ hx => Sd.oev_neg v hx,
    fun t ht x hx => by rw [sc_mul]; exact Sd.oev_smul v ht hx,
    fun σ _ hx => oev_sigR v σ hx⟩
end PI.UnitaryGroupMassFormula.LocJacTyp
