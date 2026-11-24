-- Prove2me | solution 1 for PI.WFJM.Shape.nP_add_nN_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:59.218793+00:00
-- url     : https://prove2.me/submissions/3d7b4ac8-3ab9-4148-af44-5ea0c9f89e87

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeFromFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM PI.WFJM.Shape
open PI.FJM
variable {n : ℕ}
namespace PI.WFJM.Shape
theorem _root_.solution (f : Fin n → ℚ) : nP f + nN f ≤ n := by
  classical
  unfold nP nN
  have hdis : Finset.univ.filter (fun j => 0 < f j) ∩ Finset.univ.filter (fun j => f j < 0) = ∅ := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_and, not_lt]
    intro h; exact h.le
  have h1 := Finset.card_union_add_card_inter (Finset.univ.filter (fun j => 0 < f j))
    (Finset.univ.filter (fun j => f j < 0))
  rw [hdis, Finset.card_empty, add_zero] at h1
  have h2 := Finset.card_le_univ (Finset.univ.filter (fun j => 0 < f j) ∪ Finset.univ.filter (fun j => f j < 0))
  rw [Fintype.card_fin] at h2
  omega
end PI.WFJM.Shape
