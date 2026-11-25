-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.proj_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:13:11.717773+00:00
-- url     : https://prove2.me/submissions/bac1b8b3-a138-467b-ab34-271adafd9003

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Theorems.Thm_PI_PolynomialProperness_CoreW_herm_sub_left
import Theorems.Thm_PI_PolynomialProperness_CoreW_herm_proj_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CoreW
variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.PolynomialProperness.CoreW
theorem _root_.solution (H : Matrix (Fin n) (Fin n) ℂ) (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ)
    (hG : gramOf H p * Γi = 1) (y : Fin n → ℂ) (j : ι) :
    herm H (y - proj H Γi p y) (p j) = 0 := by
  rw [herm_sub_left, herm_proj_left H Γi p hG y j, sub_self]
end PI.PolynomialProperness.CoreW
