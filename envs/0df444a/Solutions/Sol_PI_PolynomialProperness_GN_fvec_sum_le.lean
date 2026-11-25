-- Prove2me | solution 1 for PI.PolynomialProperness.GN.fvec_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:04:21.808377+00:00
-- url     : https://prove2.me/submissions/cd192f43-1c2c-4861-bedc-b03b4785e0bf

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
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) :
    ∑ i, ‖fvec k r z a i‖ ≤ 1 + ∑ i, ‖z i‖ := by
  have hz : 0 ≤ ∑ i, ‖z i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  unfold fvec
  split_ifs with h
  · have e : ∀ i, ‖bvec (eI k r ⟨a.val, h⟩) i‖ = if i = eI k r ⟨a.val, h⟩ then 1 else 0 := by
      intro i; unfold bvec; rw [Pi.single_apply]; split_ifs <;> simp
    simp only [e, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linarith
  · linarith
end PI.PolynomialProperness.GN
