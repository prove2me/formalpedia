-- Prove2me | solution 1 for PI.UnimodularOrthogonalQuadratic.Loc.det_elim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:33:54.822318+00:00
-- url     : https://prove2.me/submissions/8d1ec40f-d965-4fc9-8976-58bedaefe9a5

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
theorem _root_.solution {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) S) : (elim A).det = 1 := by
  have hlow : (elim A).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · have hj : j ≠ 0 := (ne_of_lt hij').symm
      simp [elim, Pi.single_apply, hj]
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · exact absurd hij' (Fin.not_lt_zero _)
      · have : j ≠ i := (ne_of_lt (Fin.succ_lt_succ_iff.mp hij')).symm
        simp [elim, Pi.single_apply, this]
  rw [det_of_isLowerTriangular _ hlow, Fin.prod_univ_succ]
  simp [elim]
end PI.UnimodularOrthogonalQuadratic.Loc
