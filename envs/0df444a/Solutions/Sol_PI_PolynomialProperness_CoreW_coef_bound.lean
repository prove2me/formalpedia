-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.coef_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:10:21.452657+00:00
-- url     : https://prove2.me/submissions/54ed9203-7cad-4d3c-b2a3-b90cb98bcf31

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Theorems.Thm_PI_PolynomialProperness_CoreW_eN_nonneg
import Theorems.Thm_PI_PolynomialProperness_CoreW_herm_le

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
    (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ) (R : ℝ) (hp : ∀ k, eN (p k) ≤ R)
    (y : Fin n → ℂ) (i : ι) :
    ‖coef H Γi p y i‖ ≤ (∑ j, ∑ k, ‖Γi j k‖) * (eN y * R) := by
  have hb : ∀ k, ‖herm H y (p k)‖ ≤ eN y * R := fun k =>
    (herm_le H hH hHH y (p k)).trans (mul_le_mul_of_nonneg_left (hp k) (eN_nonneg _))
  unfold coef
  simp only [Matrix.mulVec, dotProduct]
  calc ‖∑ k, Γi i k * herm H y (p k)‖ ≤ ∑ k, ‖Γi i k * herm H y (p k)‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖Γi i k‖ * (eN y * R) := Finset.sum_le_sum (fun k _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hb k) (norm_nonneg _))
    _ = (∑ k, ‖Γi i k‖) * (eN y * R) := by rw [Finset.sum_mul]
    _ ≤ (∑ j, ∑ k, ‖Γi j k‖) * (eN y * R) := by
        apply mul_le_mul_of_nonneg_right _ ((norm_nonneg _).trans (hb i))
        exact Finset.single_le_sum (f := fun j => ∑ k, ‖Γi j k‖)
          (fun j _ => Finset.sum_nonneg (fun k _ => norm_nonneg _)) (Finset.mem_univ i)
end PI.PolynomialProperness.CoreW
