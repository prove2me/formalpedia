-- Prove2me | solution 1 for PI.LocJacOrd.W.Ar.jac_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:52:21.003297+00:00
-- url     : https://prove2.me/submissions/4bc921e5-db70-4b56-a660-c61ab31a4b83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_AbsVNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocJacOrd PI.LocJacOrd.W PI.LocJacOrd.W.Ar
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacOrd
open scoped TensorProduct Classical
namespace PI.LocJacOrd.W.Ar
theorem _root_.solution (r : ℕ) (b : Fin (r + 1) → ℝ) :
    ∏ l : Fin r, ∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)), b i =
      ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then b p.1 else 1) := by
  rw [Fintype.prod_prod_type]
  simp only [Finset.prod_filter]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_succ]
  have h0 : ¬ i < (0 : Fin (r + 1)) := by simp
  rw [if_neg h0, one_mul]
  refine Finset.prod_congr rfl fun l _ => ?_
  have : (i < l.succ) ↔ ((i : ℕ) ≤ (l : ℕ)) := by
    rw [Fin.lt_def, Fin.val_succ]; omega
  simp only [this]
end PI.LocJacOrd.W.Ar
