-- Prove2me | solution 1 for PI.UnimodularOrthogonalQuadratic.Loc.det_updateRow_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:33:58.563175+00:00
-- url     : https://prove2.me/submissions/d68a1a4d-b200-4c44-a35d-4c090c476d46

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_MatOrthoLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_LocalOrthogonalMatrixOddPrime

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
theorem _root_.solution {n : ℕ} (w : Fin (n + 1) → S) :
    (updateRow (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) S) 0 w).det = w 0 := by
  have hup : (updateRow (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) S) 0 w).IsUpperTriangular := by
    intro i j hij
    have hi : i ≠ 0 := by
      rintro rfl
      exact Fin.not_lt_zero _ hij
    rw [updateRow_ne hi]
    exact one_apply_ne (ne_of_lt hij).symm
  rw [det_of_isUpperTriangular hup, Fin.prod_univ_succ]
  simp [updateRow_ne (Fin.succ_ne_zero _)]
end PI.UnimodularOrthogonalQuadratic.Loc
