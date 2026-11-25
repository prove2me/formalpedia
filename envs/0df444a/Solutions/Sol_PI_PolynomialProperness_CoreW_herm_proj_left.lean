-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.herm_proj_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:03:52.273445+00:00
-- url     : https://prove2.me/submissions/840138ed-7ccc-4519-8835-e2249ebbd8cb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Theorems.Thm_PI_PolynomialProperness_CoreW_herm_smul_left
import Theorems.Thm_PI_PolynomialProperness_CoreW_herm_sum_left

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
    herm H (proj H Γi p y) (p j) = herm H y (p j) := by
  unfold proj
  rw [herm_sum_left]
  simp only [herm_smul_left]
  have e : (∑ i, coef H Γi p y i * herm H (p i) (p j)) = (gramOf H p *ᵥ coef H Γi p y) j := by
    simp only [Matrix.mulVec, dotProduct, gramOf, Matrix.of_apply]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [e, coef, Matrix.mulVec_mulVec, hG, Matrix.one_mulVec]
end PI.PolynomialProperness.CoreW
