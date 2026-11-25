-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ClassNumImQInv.b_ne_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:27.922129+00:00
-- url     : https://prove2.me/submissions/6f41fe8b-6841-4efe-a0b6-6a8140dabb14

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticInvariants_QuadPolyIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ClassNumImQInv
open PI.ClassNumImQ
variable {d : ℕ} {K : Type} [Field K] [NumberField K] {b : K}
namespace PI.UnitaryGroupMassFormula.ClassNumImQInv
theorem _root_.solution (hq : QuadData d K b) (r : ℚ) : (r : K) ≠ b := by
  intro h
  obtain ⟨hp, -, -, hb, -⟩ := hq
  rw [← h] at hb
  have h2 : r ^ 2 = -(d : ℚ) := by exact_mod_cast hb
  have hd : (0 : ℚ) < d := by exact_mod_cast hp.pos
  nlinarith [sq_nonneg r]
end PI.UnitaryGroupMassFormula.ClassNumImQInv
