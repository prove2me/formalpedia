-- Prove2me | solution 1 for PI.OneCosetSharp.W.embedMatrix_basisVec_apply_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:07:12.694837+00:00
-- url     : https://prove2.me/submissions/488a80d1-b6cb-471a-baa7-4f2b6b773644

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_Assemble
import Theorems.Thm_PI_OneCosetSharp_W_eN_eq_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W
open Loc LocE
namespace PI.OneCosetSharp.W
theorem _root_.solution {k : Type} [Field k] {n' c n : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k))
    (tt : FC n' (c + 1) n c → k) (s : ℕ) (hs : s < n') (l : Fin (n + c)) (hl : n ≤ l.1) :
    xx1 xj tt (eN k (n' + (c + 1)) s) l = 0 := by
  have hl' : ¬ l.1 < n := not_lt.mpr hl
  rw [eN_eq_single s (by omega)]
  simp [xx1, Matrix.mulVec_single, IsFree, hs, hl', not_le.mpr hs]
end PI.OneCosetSharp.W
