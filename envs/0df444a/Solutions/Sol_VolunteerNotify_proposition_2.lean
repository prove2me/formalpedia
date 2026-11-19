-- Prove2me | solution 1 for VolunteerNotify.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-18T20:07:47.362194+00:00
-- url     : https://prove2.me/submissions/87ccd528-4238-42f8-a49d-1e34aa779b63

import Mathlib
import Definitions.Def_VolunteerNotify_IsExAnte
import Theorems.Thm_VolunteerNotify_b2_inequality

open VolunteerNotify

theorem solution {V S T : ℕ} (I : Instance V S T) (xstar : Decision V S T)
    (hx : IsExAnte I xstar) : (1 - 1 / Real.exp 1) * lpValue I ≤ f I xstar := by
  obtain ⟨xLP, xAA, xSQ, m, -, hLP, -, -, -, hfLP, -, -⟩ := hx
  -- `x*_LP` attains the supremum defining `LP_I`.
  have hval : lpValue I = lpObjective I xLP := by
    unfold lpValue
    apply IsGreatest.csSup_eq
    refine ⟨⟨xLP, hLP.1, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hLP.2 y hy
  -- Appendix B.2: termwise, `λ (1 - ∏ (1 - x p)) ≥ (1 - 1/e) λ min{∑ x p, 1}`.
  have key : (1 - 1 / Real.exp 1) * lpObjective I xLP ≤ f I xLP := by
    unfold lpObjective f
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have h := b2_inequality I xLP hLP.1 s t
    have hl := I.lam_nonneg s t
    calc (1 - 1 / Real.exp 1) * (I.lam s t * min (∑ v, xLP v s t * I.p v s) 1)
        = I.lam s t * ((1 - 1 / Real.exp 1) * min (∑ v, xLP v s t * I.p v s) 1) := by ring
      _ ≤ I.lam s t * (1 - ∏ v, (1 - xLP v s t * I.p v s)) := mul_le_mul_of_nonneg_left h hl
  rw [hval]
  linarith
