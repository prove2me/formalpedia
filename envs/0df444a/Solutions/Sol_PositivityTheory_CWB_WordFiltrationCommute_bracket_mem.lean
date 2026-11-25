-- Prove2me | solution 1 for PositivityTheory.CWB.WordFiltrationCommute.bracket_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:36:22.081951+00:00
-- url     : https://prove2.me/submissions/42a50dc8-98a4-4230-b64b-84bc1af1f94b

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnitaryGroupStatement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ParabolicUnipotentGL
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_U0Commute
import Theorems.Thm_UpperTheory_Reformulated_B_EndomorphismFiltrationMulMem_main
import Theorems.Thm_UpperTheory_Reformulated_B_ParabolicUnipotentGL_main


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
open PositivityTheory.CWB.WordFiltrationCommute
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)
namespace PositivityTheory.CWB.WordFiltrationCommute
theorem _root_.solution (hE : IsGlRep E) {j k : ℕ} {x y : Module.End ℂ V} (hx : x ∈ U E j) (hy : y ∈ U E k) :
    x * y - y * x ∈ U E (j + k - 1) :=
  by apply _root_.UpperTheory.Reformulated.B.ParabolicUnipotentGL.main <;> assumption
end PositivityTheory.CWB.WordFiltrationCommute
