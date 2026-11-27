-- Prove2me | solution 1 for PI.PolynomialProperness.GN.gN_le_of_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:32:49.3243+00:00
-- url     : https://prove2.me/submissions/918bb312-c8a8-4db7-b453-ba04013384ec

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Theorems.Thm_PI_PolynomialProperness_GN_gN_eq
import Theorems.Thm_PI_PolynomialProperness_GN_hs_le_of_entry

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
theorem _root_.solution {k r : ℕ} (g : B.Mat k r) {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, ‖g i j‖ ≤ c) :
    B.gN g ≤ (2 * r + k + 1 : ℕ) * c := by
  rw [gN_eq]
  have h1 := hs_le_of_entry g h
  rw [Fintype.card_fin] at h1
  have h2 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * c := by positivity
  calc Real.sqrt (hs g) ≤ Real.sqrt ((((2 * r + k + 1 : ℕ) : ℝ) * c) ^ 2) :=
        Real.sqrt_le_sqrt (by rw [mul_pow]; exact h1)
    _ = ((2 * r + k + 1 : ℕ) : ℝ) * c := Real.sqrt_sq h2
end PI.PolynomialProperness.GN
