-- Prove2me | solution 1 for PI.SwBig.BigCellGProof.Hpk_rhoB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:27:57.50628+00:00
-- url     : https://prove2.me/submissions/6f25c2fc-3bb4-4791-a514-1a51bfe1160d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BigCellConjugation_Monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SwBig PI.SwBig.BigCellGProof
open PI.SwBig
namespace PI.SwBig.BigCellGProof
theorem _root_.solution (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r (rhoB k r i) (rhoB k r j) = Hpk k r i j := by
  have hv : ∀ x : Fin (2 * r + k + 1), (rhoB k r x).val =
      if x.val < r ∨ r + k < x.val then 2 * r + k - x.val else x.val := by
    intro x
    unfold rhoB
    split_ifs <;> rfl
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [Fin.ext_iff, hv]
  split_ifs <;> first | rfl | (exfalso; omega)
end PI.SwBig.BigCellGProof
