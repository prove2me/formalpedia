-- Prove2me | solution 1 for PI.PolynomialProperness.GN.gN_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:03:25.948791+00:00
-- url     : https://prove2.me/submissions/d7976a5f-3536-4701-a0a0-1aff5dfd57a8

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Theorems.Thm_PI_PolynomialProperness_GN_hpk_sq
import Theorems.Thm_PI_PolynomialProperness_GN_gN_eq_frob

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
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace Matrix.frobeniusNormedRing
namespace PI.PolynomialProperness.GN
theorem _root_.solution {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : 1 ≤ B.gN g := by
  rw [gN_eq_frob]
  have hH : Hpk k r ≠ 0 := by
    intro h0
    have := hpk_sq k r
    rw [h0, Matrix.zero_mul] at this
    exact zero_ne_one this
  have hpos : 0 < ‖Hpk k r‖ := norm_pos_iff.mpr hH
  have h1 : ‖Hpk k r‖ ≤ ‖g‖ * ‖Hpk k r‖ * ‖g‖ := by
    have e : gᴴ * Hpk k r * g = Hpk k r := hg
    calc ‖Hpk k r‖ = ‖gᴴ * Hpk k r * g‖ := by rw [e]
      _ ≤ ‖gᴴ * Hpk k r‖ * ‖g‖ := Matrix.frobenius_norm_mul _ _
      _ ≤ ‖gᴴ‖ * ‖Hpk k r‖ * ‖g‖ :=
          mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _)
      _ = ‖g‖ * ‖Hpk k r‖ * ‖g‖ := by rw [Matrix.frobenius_norm_conjTranspose]
  by_contra hlt
  rw [not_le] at hlt
  have hg0 : 0 ≤ ‖g‖ := norm_nonneg _
  have : ‖g‖ * ‖Hpk k r‖ * ‖g‖ < ‖Hpk k r‖ := by nlinarith [mul_nonneg hg0 hpos.le]
  linarith
end PI.PolynomialProperness.GN
