-- Prove2me | solution 1 for PositivityTheory.CWB.word_filtration_of_length
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:10.680175+00:00
-- url     : https://prove2.me/submissions/bffbe375-0fbe-41a2-bbde-eaea0aa45c8e

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnitaryGroupStatement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ParabolicUnipotentGL
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_U0Commute
import Theorems.Thm_PositivityTheory_CWB_WordFiltrationCommute_U_mono
import Theorems.Thm_PositivityTheory_CWB_WordFiltrationCommute_one_mem
import Theorems.Thm_PositivityTheory_CWB_WordFiltrationCommute_gen_mem
import Theorems.Thm_PositivityTheory_CWB_WordFiltrationCommute_mul_mem
import Theorems.Thm_PositivityTheory_CWB_WordFiltrationCommute_bracket_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CWB
open PositivityTheory.CW
namespace PositivityTheory.CWB
theorem _root_.solution : A1 := by
  intro n ε V _ _ E hM
  have hE : IsGlRep E := hM.gl
  have hC : casimirK ε E ∈ U E 2 := by
    unfold casimirK
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    exact WordFiltrationCommute.U_mono E (by norm_num : 1 + 1 ≤ 2) (WordFiltrationCommute.mul_mem E (WordFiltrationCommute.gen_mem E a b) (WordFiltrationCommute.gen_mem E b a))
  refine ⟨fun j k h => WordFiltrationCommute.U_mono E h, WordFiltrationCommute.one_mem E, WordFiltrationCommute.gen_mem E,
    fun j k x hx y hy => WordFiltrationCommute.mul_mem E hx hy, fun j k x hx y hy => WordFiltrationCommute.bracket_mem E hE hx hy, hC,
    fun a b => ?_⟩
  have hZ := WordFiltrationCommute.bracket_mem E hE hC (WordFiltrationCommute.gen_mem E a b)
  unfold Z
  exact WordFiltrationCommute.U_mono E (by norm_num : 2 + 1 - 1 ≤ 2) hZ
end PositivityTheory.CWB
