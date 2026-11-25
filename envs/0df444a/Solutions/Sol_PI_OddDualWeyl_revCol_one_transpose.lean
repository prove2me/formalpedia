-- Prove2me | solution 1 for PI.OddDualWeyl.revCol_one_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:59:09.100007+00:00
-- url     : https://prove2.me/submissions/5b7a01ae-ab99-4a12-8715-8bfc4e509f13

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_RevColOneTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
variable {K : Type} [Field K]
namespace PI.OddDualWeyl
theorem _root_.solution {m : ℕ} : (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K))ᵀ = revCol 1 := by
  ext i j
  simp only [revCol, transpose_apply, submatrix_apply, id_eq, one_apply]
  have h : (j = i.rev) ↔ (i = j.rev) :=
    ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  by_cases hij : i = j.rev
  · rw [if_pos hij, if_pos (h.mpr hij)]
  · rw [if_neg hij, if_neg (fun h' => hij (h.mp h'))]
end PI.OddDualWeyl
