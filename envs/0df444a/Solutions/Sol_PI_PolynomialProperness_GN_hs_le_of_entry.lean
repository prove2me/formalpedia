-- Prove2me | solution 1 for PI.PolynomialProperness.GN.hs_le_of_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:04:11.754509+00:00
-- url     : https://prove2.me/submissions/b1ad7a5c-faed-4e6f-ba53-3c5468269cc8

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound

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
theorem _root_.solution {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) {c : ℝ}
    (h : ∀ i j, ‖M i j‖ ≤ c) : hs M ≤ (Fintype.card ι : ℝ) ^ 2 * c ^ 2 := by
  unfold hs
  have h1 : ∀ i j, Complex.normSq (M i j) ≤ c ^ 2 := by
    intro i j
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
  calc ∑ i, ∑ j, Complex.normSq (M i j) ≤ ∑ _i : ι, ∑ _j : ι, c ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
    _ = (Fintype.card ι : ℝ) ^ 2 * c ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
end PI.PolynomialProperness.GN
