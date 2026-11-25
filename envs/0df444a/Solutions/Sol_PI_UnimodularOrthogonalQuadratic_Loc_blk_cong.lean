-- Prove2me | solution 1 for PI.UnimodularOrthogonalQuadratic.Loc.blk_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:33:32.879578+00:00
-- url     : https://prove2.me/submissions/f907ef85-174e-4099-b963-d44c8dfbf872

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
theorem _root_.solution {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) S} {P : Matrix (Fin n) (Fin n) S}
    (hrow : ∀ b, M 0 b = if b = 0 then 1 else 0) (hcol : ∀ a, M a 0 = if a = 0 then 1 else 0)
    (hP : P * M.submatrix Fin.succ Fin.succ * Pᴴ = 1) : blk P * M * (blk P)ᴴ = 1 := by
  have hr0 : M 0 0 = 1 := by simp [hrow]
  have hrs : ∀ j : Fin n, M 0 j.succ = 0 := fun j => by simp [hrow, Fin.succ_ne_zero]
  have hcs : ∀ i : Fin n, M i.succ 0 = 0 := fun i => by simp [hcol, Fin.succ_ne_zero]
  ext a b
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨j, rfl⟩
  · simp [blk, mul_apply, Fin.sum_univ_succ, hr0, hrs, hcs, one_apply]
  · simp [blk, mul_apply, Fin.sum_univ_succ, hr0, hrs, hcs, one_apply, (Fin.succ_ne_zero j).symm]
  · simp [blk, mul_apply, Fin.sum_univ_succ, hr0, hrs, hcs, one_apply]
  · have := congrFun (congrFun hP i) j
    simp only [mul_apply, submatrix_apply, conjTranspose_apply] at this
    simp [blk, mul_apply, Fin.sum_univ_succ, hr0, hrs, hcs, one_apply] at this ⊢
    exact this
end PI.UnimodularOrthogonalQuadratic.Loc
