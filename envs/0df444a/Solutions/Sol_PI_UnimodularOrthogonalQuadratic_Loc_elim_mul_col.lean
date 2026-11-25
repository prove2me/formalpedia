-- Prove2me | solution 1 for PI.UnimodularOrthogonalQuadratic.Loc.elim_mul_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:34:03.951905+00:00
-- url     : https://prove2.me/submissions/78693bc6-7275-4a46-b9cf-38c7b3828c8a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_MatOrthoLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_LocalOrthogonalMatrixOddPrime
import Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_elimination_mul_first_row

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnimodularOrthogonalQuadratic PI.UnimodularOrthogonalQuadratic.Loc
open Matrix
variable {S : Type} [CommRing S] [StarRing S]
namespace PI.UnimodularOrthogonalQuadratic.Loc
theorem _root_.solution {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) S} (h : A 0 0 = 1) (a : Fin (n + 1)) :
    (elim A * A) a 0 = if a = 0 then 1 else 0 := by
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩
  · simp [elimination_mul_first_row, h]
  · simp [elim, mul_apply, Fin.sum_univ_succ, h, Pi.single_apply, Fin.succ_ne_zero]
end PI.UnimodularOrthogonalQuadratic.Loc
