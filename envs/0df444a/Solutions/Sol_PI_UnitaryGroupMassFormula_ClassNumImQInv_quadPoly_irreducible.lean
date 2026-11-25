-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ClassNumImQInv.quadPoly_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:30.752669+00:00
-- url     : https://prove2.me/submissions/490ceb5e-1620-4481-9d12-e36cfac158fd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticInvariants_QuadPolyIrreducible
import Theorems.Thm_PI_UnitaryGroupMassFormula_ClassNumImQInv_quadPoly_natDegree

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
theorem _root_.solution (hq : QuadData d K b) : Irreducible (quadPoly d) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [quadPoly_natDegree]; simp
  · intro x hx
    obtain ⟨hp, -, -, -, -⟩ := hq
    unfold quadPoly at hx
    simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hx
    have hd : (0 : ℚ) < d := by exact_mod_cast hp.pos
    nlinarith [sq_nonneg x]
end PI.UnitaryGroupMassFormula.ClassNumImQInv
