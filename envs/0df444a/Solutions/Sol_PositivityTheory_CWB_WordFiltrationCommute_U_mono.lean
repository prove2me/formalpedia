-- Prove2me | solution 1 for PositivityTheory.CWB.WordFiltrationCommute.U_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:33:10.552605+00:00
-- url     : https://prove2.me/submissions/90ed7cee-736e-4d4e-b87f-87753f261966

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
theorem _root_.solution {j k : ℕ} (h : j ≤ k) : U E j ≤ U E k :=
  Submodule.span_mono fun _ ⟨l, hl, hx⟩ => ⟨l, hl.trans h, hx⟩
end PositivityTheory.CWB.WordFiltrationCommute
