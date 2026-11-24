-- Prove2me | solution 1 for PI.FockWtDegWork.sum_diag_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:43.423047+00:00
-- url     : https://prove2.me/submissions/29779035-81ab-4815-8d2c-b8b57c00c088

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockWtDegWork
namespace PI.FockWtDegWork
theorem _root_.solution {p q r s : ℕ} (M : Matrix (Ln p q r s) (Ln p q r s) ℂ)
    (g : Ln p q r s → Prop) [DecidablePred g]
    (hM : ∀ l l', M l l' = if l = l' ∧ g l then 1 else 0) :
    ∑ l, ∑ l', M l l' • omE l l' = ∑ l, if g l then omE l l else 0 := by
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l]
  · rw [hM]
    by_cases h : g l <;> simp [h]
  · intro l' _ hne
    rw [hM, if_neg (show ¬ (l = l' ∧ g l) from fun h => hne h.1.symm), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ l) h
end PI.FockWtDegWork
