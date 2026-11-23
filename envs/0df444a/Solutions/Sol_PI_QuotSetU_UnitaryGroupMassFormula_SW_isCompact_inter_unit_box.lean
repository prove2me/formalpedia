-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.isCompact_inter_unit_box
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:21.306495+00:00
-- url     : https://prove2.me/submissions/7f9ba345-0d0c-40ab-8835-58c6cd2f2dd3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsClosedS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsCompactInterUnitBox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} {D : Matrix (Fin m) (Fin m) ℂ → ℝ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution (hG : IsClosed G) : IsCompact (G ∩ box1 m) := by
  have hbox : box1 m = Set.pi Set.univ (fun i => Set.pi Set.univ
      (fun j => Metric.closedBall ((1 : Matrix (Fin m) (Fin m) ℂ) i j) 1)) := by
    ext x
    simp only [box1, Set.mem_setOf_eq, Matrix.sub_apply]
    constructor
    · intro h
      show ∀ i ∈ Set.univ, ∀ j ∈ Set.univ, x i j ∈ Metric.closedBall ((1 : Matrix (Fin m) (Fin m) ℂ) i j) 1
      intro i _ j _
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact h i j
    · intro h i j
      have h' : ∀ i ∈ Set.univ, ∀ j ∈ Set.univ, x i j ∈ Metric.closedBall ((1 : Matrix (Fin m) (Fin m) ℂ) i j) 1 := h
      have h2 := h' i (Set.mem_univ _) j (Set.mem_univ _)
      rw [Metric.mem_closedBall, dist_eq_norm] at h2
      exact h2
  have hc : IsCompact (box1 m) := by
    rw [hbox]
    exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _
  exact hc.inter_left hG
end PI.QuotSetU.UnitaryGroupMassFormula.SW
