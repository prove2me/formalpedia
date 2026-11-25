-- Prove2me | solution 1 for PositivityTheory.CWB.WordFiltrationCommute.one_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:25:54.436271+00:00
-- url     : https://prove2.me/submissions/709a3050-ff3f-4c6b-878d-5901e78bb519

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnitaryGroupStatement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ParabolicUnipotentGL
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_U0Commute

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
theorem _root_.solution : (1 : Module.End ℂ V) ∈ U E 0 :=
  Submodule.subset_span ⟨[], by simp, by simp⟩
end PositivityTheory.CWB.WordFiltrationCommute
