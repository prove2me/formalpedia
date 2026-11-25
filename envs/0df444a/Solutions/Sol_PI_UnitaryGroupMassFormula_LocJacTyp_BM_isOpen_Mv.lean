-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.BM.isOpen_Mv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:39.083655+00:00
-- url     : https://prove2.me/submissions/45e2d0f1-8980-4d46-b164-442cb2c48470

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiscreteHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_LocPowB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulA
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_isOpen_Ov

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp.BM
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped ENNReal NNReal Pointwise
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.LocJacTyp.BM
theorem _root_.solution (ϖ : Fv F v) : IsOpen (Mv v ϖ) := (isOpen_Ov v).preimage (continuous_mul_left _)
end PI.UnitaryGroupMassFormula.LocJacTyp.BM
