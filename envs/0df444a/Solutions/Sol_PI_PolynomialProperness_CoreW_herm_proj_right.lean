-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.herm_proj_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:24:36.338722+00:00
-- url     : https://prove2.me/submissions/404d7451-a93d-43f6-8a1d-9b667cc23473

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Theorems.Thm_PI_PolynomialProperness_CoreW_herm_smul_right
import Theorems.Thm_PI_PolynomialProperness_CoreW_herm_sum_right

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
theorem _root_.solution (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (Γi : Matrix ι ι ℂ)
    (p : ι → Fin n → ℂ) (y x : Fin n → ℂ) (hx : ∀ j, herm H x (p j) = 0) :
    herm H x (proj H Γi p y) = 0 := by
  unfold proj
  rw [herm_sum_right H hH]
  simp [herm_smul_right H hH, hx]
end PI.PolynomialProperness.CoreW
