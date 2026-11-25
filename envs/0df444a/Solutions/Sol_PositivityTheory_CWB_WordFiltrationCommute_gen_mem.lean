-- Prove2me | solution 1 for PositivityTheory.CWB.WordFiltrationCommute.gen_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:36:24.999059+00:00
-- url     : https://prove2.me/submissions/b68da8c1-1523-4df0-abcc-5e504974bc6a

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
theorem _root_.solution (a b : Fin n) : E a b ∈ U E 1 :=
  Submodule.subset_span ⟨[(a, b)], by simp, by simp⟩
end PositivityTheory.CWB.WordFiltrationCommute
