-- Prove2me | solution 1 for PositivityTheory.CW.CasimirRealScalar.casimir_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:23:52.383161+00:00
-- url     : https://prove2.me/submissions/81082b96-4ae3-4a68-b1d7-afc9c99e0e54

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CasimirRealOfCentral

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
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.CasimirRealScalar
variable {n : ℕ}
namespace PositivityTheory.CW.CasimirRealScalar
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) :
    casimir E = (Mm E ^ 2).trace := by
  unfold casimir Mm
  rw [sq, Matrix.trace]
  simp [Matrix.diag, Matrix.mul_apply]
end PositivityTheory.CW.CasimirRealScalar
