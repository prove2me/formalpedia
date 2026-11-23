-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BesselLevi.colX_of_left_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:37.118103+00:00
-- url     : https://prove2.me/submissions/a99f047c-cc66-448a-8ab8-9ee1ef216469

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselLevi
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselLeviAction_MulVecBvecApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BesselLevi
variable {k r : ℕ}
namespace PI.UnitaryGroupMassFormula.BesselLevi
theorem _root_.solution {g g' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : colX k r g) (hm : g' * g = 1) : colX k r g' := by
  suffices H : ∀ m, ∀ i j : Fin (2 * r + k + 1), j.val = m → j.val < r → j.val ≤ i.val →
      g' i j = if i = j then 1 else 0 from fun i j hj hji => H _ i j rfl hj hji
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i j hjm hj hji
    have e := congrFun (congrFun hm i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    have hterm : ∀ l, g' i l * g l j = if l = j then g' i j else 0 := by
      intro l
      by_cases hl : l.val < j.val
      · have h0 : g' i l = 0 := by
          rw [ih l.val (by omega) i l rfl (by omega) (by omega), if_neg]
          intro hil
          subst hil
          omega
        rw [h0, zero_mul, if_neg]
        intro hlj
        subst hlj
        omega
      · rw [hg l j hj (by omega)]
        by_cases hlj : l = j
        · subst hlj
          simp
        · simp [hlj]
    rw [Finset.sum_congr rfl (fun l _ => hterm l)] at e
    simpa using e
end PI.UnitaryGroupMassFormula.BesselLevi
