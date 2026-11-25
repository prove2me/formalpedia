-- Prove2me | solution 1 for PI.UConjT.submatrix_mem_unitaryGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:32:40.559267+00:00
-- url     : https://prove2.me/submissions/ea282183-4de2-41d4-8e1d-41ae7821eabc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_TransferStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_SubmatrixMemUnitaryGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UConjT
open Matrix
namespace PI.UConjT
theorem _root_.solution {n : ℕ} (k : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hk : k ∈ unitaryGroup (Fin (n + 1)) ℂ) (hcol : ∀ i, k (Fin.castSucc i) (Fin.last n) = 0) :
    k.submatrix Fin.castSucc Fin.castSucc ∈ unitaryGroup (Fin n) ℂ := by
  rw [mem_unitaryGroup_iff] at hk ⊢
  ext a b
  have hab := congrFun (congrFun hk (Fin.castSucc a)) (Fin.castSucc b)
  rw [mul_apply, Fin.sum_univ_castSucc] at hab
  simp only [star_eq_conjTranspose, conjTranspose_apply, hcol, zero_mul, add_zero,
    one_apply, Fin.castSucc_inj] at hab
  simpa [mul_apply, conjTranspose_apply, one_apply] using hab
end PI.UConjT
