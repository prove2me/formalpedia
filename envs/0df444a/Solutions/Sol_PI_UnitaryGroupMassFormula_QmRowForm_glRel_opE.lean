-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmRowForm.glRel_opE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:17.0508+00:00
-- url     : https://prove2.me/submissions/3b970cad-46b6-437f-9189-1b98e0651aee

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_DoubleRowIncreasing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmRowForm
namespace PI.UnitaryGroupMassFormula.QmRowForm
theorem _root_.solution {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) : GlRel (opE E) := by
  intro a b c d
  have h := hE d c b a
  show MulOpposite.op (E b a) * MulOpposite.op (E d c) - MulOpposite.op (E d c) * MulOpposite.op (E b a) =
    (if b = c then MulOpposite.op (E d a) else 0) - (if d = a then MulOpposite.op (E b c) else 0)
  rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, ← MulOpposite.op_sub, h]
  clear h hE
  split_ifs <;> simp_all
end PI.UnitaryGroupMassFormula.QmRowForm
