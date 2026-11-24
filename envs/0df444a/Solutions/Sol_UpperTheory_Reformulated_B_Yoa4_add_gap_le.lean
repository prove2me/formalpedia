-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Yoa4.add_gap_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:35:14.296161+00:00
-- url     : https://prove2.me/submissions/88c49873-88ea-408a-b24f-bd3a7352ee22

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AddGapLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Yoa4
theorem _root_.solution :
    ∀ {r : ℕ} {d : Fin r → ℕ}, StrictAnti d → ∀ (k : ℕ) (i j : Fin r), (↑j : ℕ) = (↑i : ℕ) + k → d j + k ≤ d i := by
  intro r d hd k
  induction k with
  | zero =>
    intro i j h
    have hij : j = i := Fin.ext (by simpa using h)
    subst hij
    simp
  | succ k ih =>
    intro i j h
    have hj := j.isLt
    have hm : (i : ℕ) + k < r := by omega
    have h1 := ih i ⟨(i : ℕ) + k, hm⟩ rfl
    have h2 : d j < d ⟨(i : ℕ) + k, hm⟩ := hd (by
      rw [Fin.lt_def]
      simp only
      omega)
    omega
end UpperTheory.Reformulated.B.Yoa4
