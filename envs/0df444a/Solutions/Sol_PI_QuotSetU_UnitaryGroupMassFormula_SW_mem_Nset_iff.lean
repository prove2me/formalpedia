-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.mem_Nset_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:14:52.323012+00:00
-- url     : https://prove2.me/submissions/07099d7e-d129-4d0f-b754-ba08ab0ccebd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup

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
variable {k r : ℕ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    g ∈ Nset k r ↔ g ∈ UH (Hpk k r) ∧ NC k r g := by
  simp only [Nset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hU, h2, h3⟩
    refine ⟨hU, fun i j hj hi => ?_⟩
    by_cases hjr : j.val < r
    · have hej : eI k r ⟨j.val, hjr⟩ = j := Fin.ext (by simp [eI])
      have h := h2 ⟨j.val, hjr⟩ i (by rw [min_eq_left hjr.le] at hi; exact hi)
      rwa [hej] at h
    · push_neg at hjr
      exact h3 i j hjr hj (by rwa [min_eq_right hjr] at hi)
  · rintro ⟨hU, hN⟩
    refine ⟨hU, fun a i hai => ?_, fun i j hj1 hj2 hi => ?_⟩
    · have hv : (eI k r a).val = a.val := by simp [eI]
      exact hN i (eI k r a) (by rw [hv]; omega) (by rw [hv, min_eq_left a.isLt.le]; exact hai)
    · exact hN i j hj2 (by rw [min_eq_right hj1]; exact hi)
end PI.QuotSetU.UnitaryGroupMassFormula.SW
