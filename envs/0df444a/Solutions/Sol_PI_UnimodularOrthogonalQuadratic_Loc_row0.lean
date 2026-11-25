-- Prove2me | solution 1 for PI.UnimodularOrthogonalQuadratic.Loc.row0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:39:29.646716+00:00
-- url     : https://prove2.me/submissions/6f86438e-2600-4ac2-9e03-88e37d88e15f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_MatOrthoLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_LocalOrthogonalMatrixOddPrime
import Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_elimination_mul_first_row
import Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_elim_mul_col

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
theorem _root_.solution {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) S} (hA : Aᴴ = A) (h : A 0 0 = 1) (b : Fin (n + 1)) :
    (elim A * A * (elim A)ᴴ) 0 b = if b = 0 then 1 else 0 := by
  have e1 : (elim A * A * (elim A)ᴴ) 0 b = (A * (elim A)ᴴ) 0 b := by
    rw [mul_apply (M := elim A * A), mul_apply (M := A)]
    exact Finset.sum_congr rfl fun l _ => by rw [elimination_mul_first_row]
  rw [e1, show A * (elim A)ᴴ = (elim A * A)ᴴ by rw [conjTranspose_mul, hA], conjTranspose_apply,
    elim_mul_col h]
  split_ifs <;> simp
end PI.UnimodularOrthogonalQuadratic.Loc
