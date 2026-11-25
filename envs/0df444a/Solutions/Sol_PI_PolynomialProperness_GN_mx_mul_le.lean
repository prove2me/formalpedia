-- Prove2me | solution 1 for PI.PolynomialProperness.GN.mx_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:22:08.41455+00:00
-- url     : https://prove2.me/submissions/ebd385fd-7b6e-4a63-893f-5235f871089b

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Theorems.Thm_PI_PolynomialProperness_GN_mx_nonneg
import Theorems.Thm_PI_PolynomialProperness_GN_entry_le_mx
import Theorems.Thm_PI_PolynomialProperness_GN_mx_le_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.GN
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
namespace PI.PolynomialProperness.GN
theorem _root_.solution {m : ℕ} (A B' : Matrix (Fin m) (Fin m) ℂ) :
    C2.mx (A * B') ≤ m * C2.mx A * C2.mx B' := by
  have h0 : 0 ≤ (m : ℝ) * C2.mx A * C2.mx B' := by
    have := mx_nonneg A; have := mx_nonneg B'; positivity
  refine (mx_le_iff _ h0).2 fun i j => ?_
  rw [mul_apply]
  calc ‖∑ l, A i l * B' l j‖ ≤ ∑ l, ‖A i l * B' l j‖ := norm_sum_le _ _
    _ ≤ ∑ _l : Fin m, C2.mx A * C2.mx B' := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [norm_mul]
        exact mul_le_mul (entry_le_mx A i l) (entry_le_mx B' l j) (norm_nonneg _) (mx_nonneg A)
    _ = m * C2.mx A * C2.mx B' := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
end PI.PolynomialProperness.GN
