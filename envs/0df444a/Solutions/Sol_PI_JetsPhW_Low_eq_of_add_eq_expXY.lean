-- Prove2me | solution 1 for PI.JetsPhW.Low.eq_of_add_eq_expXY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:46:57.025714+00:00
-- url     : https://prove2.me/submissions/c2d42023-b6fb-4bdb-a273-bf03e28e3cf2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.Low
variable {K : Type*} [CommRing K]
namespace PI.JetsPhW.Low
theorem _root_.solution {x y : Fin 2 →₀ ℕ} (hxy : x + y = bivariateExponentMonomial) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x = E0 ∧ y = E1) ∨ (x = E1 ∧ y = E0) := by
  have h0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) hxy
  have h1 := congrArg (fun d : Fin 2 →₀ ℕ => d 1) hxy
  simp only [Finsupp.add_apply, Finsupp.single_apply] at h0 h1
  norm_num at h0 h1
  have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (Finsupp.ext (fun i => by fin_cases i <;> simp [hc.1, hc.2]))
  have hy' : y 0 ≠ 0 ∨ y 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hy (Finsupp.ext (fun i => by fin_cases i <;> simp [hc.1, hc.2]))
  rcases Nat.eq_zero_or_pos (x 0) with a0 | a0
  · right
    refine ⟨Finsupp.ext (fun i => ?_), Finsupp.ext (fun i => ?_)⟩ <;> fin_cases i <;>
      simp <;> omega
  · left
    refine ⟨Finsupp.ext (fun i => ?_), Finsupp.ext (fun i => ?_)⟩ <;> fin_cases i <;>
      simp <;> omega
end PI.JetsPhW.Low
