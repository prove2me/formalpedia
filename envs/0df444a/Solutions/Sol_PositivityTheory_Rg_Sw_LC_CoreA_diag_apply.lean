-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreA.diag_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:08.0854+00:00
-- url     : https://prove2.me/submissions/8c4d3f48-d9c7-436e-819a-7f05578cfc3d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SupPerp
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_DiagApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreA
variable {V : Type} [AddCommGroup V] [Module ℂ V] {φ : V → V → ℂ}
namespace PositivityTheory.Rg.Sw.LC.CoreA
theorem _root_.solution (d : ℕ) (f : Module.End ℂ V) (w : Fin d → V) (k : Fin d) : diag d f w k = f (w k) := by
  simp [diag]
end PositivityTheory.Rg.Sw.LC.CoreA
