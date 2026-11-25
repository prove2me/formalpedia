-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.BM.index_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:59:41.477309+00:00
-- url     : https://prove2.me/submissions/07e26482-0350-45c1-9f1e-4e64a980e8c2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiscreteHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_LocPowB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_ul_card_residue_eq


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
theorem _root_.solution : (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup.index =
    Ideal.absNorm v.asIdeal := by
  rw [← ReciprocityTheory.DiscreteGroups.GlobalClassField.ul_card_residue_eq F v]
  show Submodule.cardQuot _ = _
  rw [Submodule.cardQuot_apply]
  rfl
end PI.UnitaryGroupMassFormula.LocJacTyp.BM
