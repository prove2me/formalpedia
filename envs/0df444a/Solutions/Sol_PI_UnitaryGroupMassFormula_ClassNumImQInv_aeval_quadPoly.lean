-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ClassNumImQInv.aeval_quadPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:38:27.922209+00:00
-- url     : https://prove2.me/submissions/24207ff1-82f8-4ee5-b2da-0040fca567f7

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
theorem _root_.solution (hq : QuadData d K b) : aeval b (quadPoly d) = 0 := by
  obtain ⟨-, -, -, hb, -⟩ := hq
  unfold quadPoly
  simp [hb]
end PI.UnitaryGroupMassFormula.ClassNumImQInv
