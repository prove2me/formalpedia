-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.lincomb_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:36:33.827154+00:00
-- url     : https://prove2.me/submissions/afd778d7-17dd-428c-90de-1d6efcb73e0e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Theorems.Thm_PI_PolynomialProperness_CoreW_eN_nonneg
import Theorems.Thm_PI_PolynomialProperness_CoreW_eN_smul
import Theorems.Thm_PI_PolynomialProperness_CoreW_eN_sum

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
theorem _root_.solution (c : ι → ℂ) (q : ι → Fin n → ℂ) (a R : ℝ) (_hR : 0 ≤ R)
    (hc : ∀ i, ‖c i‖ ≤ a) (hq : ∀ i, eN (q i) ≤ R) :
    eN (∑ i, c i • q i) ≤ (Fintype.card ι : ℝ) * a * R := by
  calc eN (∑ i, c i • q i) ≤ ∑ i, eN (c i • q i) := eN_sum _ _
    _ = ∑ i, ‖c i‖ * eN (q i) := by simp only [eN_smul]
    _ ≤ ∑ _i : ι, a * R := Finset.sum_le_sum (fun i _ =>
        mul_le_mul (hc i) (hq i) (eN_nonneg _) ((norm_nonneg _).trans (hc i)))
    _ = (Fintype.card ι : ℝ) * a * R := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
end PI.PolynomialProperness.CoreW
