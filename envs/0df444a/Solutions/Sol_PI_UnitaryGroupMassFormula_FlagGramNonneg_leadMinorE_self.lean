-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FlagGramNonneg.leadMinorE_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:25.396531+00:00
-- url     : https://prove2.me/submissions/87608eff-bfe4-4def-a076-49fbdc5a48ab

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_NatAddZeroFinOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg
namespace PI.UnitaryGroupMassFormula.FlagGramNonneg
theorem _root_.solution {E : Type} [Field E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    leadMinorE Z r = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  unfold leadMinorE
  rw [dif_pos (Nat.le_succ r)]
  rfl
end PI.UnitaryGroupMassFormula.FlagGramNonneg
