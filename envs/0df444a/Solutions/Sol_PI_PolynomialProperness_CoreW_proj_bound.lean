-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.proj_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:23:54.322926+00:00
-- url     : https://prove2.me/submissions/0b369427-2510-4d1a-bc6d-c9b26c0a97c9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Theorems.Thm_PI_PolynomialProperness_CoreW_lincomb_bound
import Theorems.Thm_PI_PolynomialProperness_CoreW_coef_bound

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
theorem _root_.solution (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ) (R : ℝ) (hR : 0 ≤ R) (hp : ∀ k, eN (p k) ≤ R)
    (y : Fin n → ℂ) :
    eN (proj H Γi p y) ≤
      (Fintype.card ι : ℝ) * ((∑ j, ∑ k, ‖Γi j k‖) * (eN y * R)) * R :=
  lincomb_bound _ _ _ R hR (fun i => coef_bound H hH hHH Γi p R hp y i) hp
end PI.PolynomialProperness.CoreW
