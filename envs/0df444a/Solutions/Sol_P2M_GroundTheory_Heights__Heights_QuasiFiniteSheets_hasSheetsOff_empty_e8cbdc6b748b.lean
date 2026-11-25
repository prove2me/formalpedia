-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_QuasiFiniteSheets_hasSheetsOff_empty_e8cbdc6b748b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:52.388048+00:00
-- url     : https://prove2.me/submissions/947f288e-8f85-4139-b44a-278f42a0c6e7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimeQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimePairMeetImage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PQuasiFiniteSheets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.QuasiFiniteSheets
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.QuasiFiniteSheets
theorem _root_.solution (A : Matrix (Fin d) (Fin n) ℂ) : HasSheetsOff ∅ A 1 := by
  intro y _
  refine ⟨Set.univ, 0, Fin.elim0, isOpen_univ, Set.mem_univ _, fun j => j.elim0, fun y' _ => ?_⟩
  refine ⟨fun j => j.elim0, fun i => i.elim0, ?_⟩
  rintro x ⟨hx, -⟩
  exact hx.elim
end GroundTheory.Heights₂.Heights.QuasiFiniteSheets
