-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.uw_col_out
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:51.774129+00:00
-- url     : https://prove2.me/submissions/f0486529-72d7-4d6f-bb9e-0000995cc4eb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mulVec_bvec_apply
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_bvec_apply

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
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (j : Fin (2 * r + k + 1)) (hj : ¬ inW k r j) (i : Fin (2 * r + k + 1)) :
    h i j = if i = j then 1 else 0 := by
  simp only [UWset, Set.mem_setOf_eq] at hh
  obtain ⟨-, hfix, -⟩ := hh
  have key : h *ᵥ bvec j = bvec j := by
    unfold inW at hj
    by_cases hjr : j.val < r
    · have h1 := (hfix ⟨j.val, hjr⟩).1
      have e : eI k r ⟨j.val, hjr⟩ = j := Fin.ext rfl
      rwa [e] at h1
    · have ha : 2 * r + k - j.val < r := by
        have := j.isLt
        omega
      have h1 := (hfix ⟨2 * r + k - j.val, ha⟩).2
      have e : esI k r ⟨2 * r + k - j.val, ha⟩ = j := by
        apply Fin.ext
        show 2 * r + k - (2 * r + k - j.val) = j.val
        have := j.isLt
        omega
      rwa [e] at h1
  rw [← mulVec_bvec_apply h i j, key, bvec_apply]
end PI.QuotSetU.UnitaryGroupMassFormula.SW
