-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.WbDefC.linIndep_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:48.122653+00:00
-- url     : https://prove2.me/submissions/9a72ab4f-a807-44af-b2a2-57b7f0847ae4

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Lemmata_MiscLemmasI_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_CTEqConjTranspose
import Theorems.Thm_Bl_SecondBlockLemmaJ_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula PI.UnitaryGroupMassFormula.CntFormula.WbDefC
namespace PI.UnitaryGroupMassFormula.CntFormula.WbDefC
theorem _root_.solution {K L ι n : Type} [Field K] [Field L] [Fintype ι] [Fintype n] [DecidableEq ι]
    [DecidableEq n] (τ : K →+* L) (c : ι → n → K) (hc : LinearIndependent K c) :
    LinearIndependent L (fun a => fun i => τ (c a i)) := by
  first | exact Bl.SecondBlockLemmaJ.goal1 .. | (apply Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaJ.goal1 <;> first | assumption | infer_instance)
end PI.UnitaryGroupMassFormula.CntFormula.WbDefC
