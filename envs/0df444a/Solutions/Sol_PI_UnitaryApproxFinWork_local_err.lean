-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.local_err
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:34:17.282487+00:00
-- url     : https://prove2.me/submissions/ba1ea0eb-e85e-4a16-aeef-6b3a8e6b0fd0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_SkewApprox
import Definitions.Def_Lemmata_GeneralBFactRightTer_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Assembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork
namespace PI.UnitaryApproxFinWork
theorem _root_.solution {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (h2 : IsUnit (2 : R)) (g X XR W N γR : Matrix n n R)
    (hXP : (1 + X) * (1 + g) = 2) (hΔ' : (XR - X) * (1 + g) = (2 : R) • W) (hN : (1 + W) * N = 1)
    (hγ' : γR * (1 + XR) = 1 - XR) :
    g - γR = (1 + g) * W * N := by
  obtain ⟨Δ, rfl⟩ : ∃ Δ, XR = X + Δ := ⟨XR - X, by abel⟩
  have hΔ : Δ * (1 + g) = (2 : R) • W := by rwa [add_sub_cancel_left] at hΔ'
  have hγ : γR * (1 + (X + Δ)) = 1 - (X + Δ) := hγ'
  have h2m : (2 : Matrix n n R) = (2 : R) • 1 := by rw [two_smul, one_add_one_eq_two]
  have hQP : (1 + (X + Δ)) * (1 + g) = (2 : R) • (1 + W) := by
    rw [← add_assoc, Matrix.add_mul, hXP, hΔ, h2m, smul_add]
  have key : (2 : R) • (γR * (1 + W)) = (2 : R) • ((1 + g) - (1 + W)) := by
    have e1 : γR * ((2 : R) • (1 + W)) = (1 - (X + Δ)) * (1 + g) := by
      rw [← hQP, ← Matrix.mul_assoc, hγ]
    rw [← Matrix.mul_smul, e1, smul_sub, ← hQP]
    have e2 : (1 - (X + Δ)) * (1 + g) = (2 : R) • (1 + g) - (1 + (X + Δ)) * (1 + g) := by
      rw [two_smul]; noncomm_ring
    rw [e2]
  have k2 := h2.smul_left_cancel.mp key
  calc g - γR = g * ((1 + W) * N) - γR * ((1 + W) * N) := by rw [hN, Matrix.mul_one, Matrix.mul_one]
    _ = g * ((1 + W) * N) - (γR * (1 + W)) * N := by rw [Matrix.mul_assoc]
    _ = (1 + g) * W * N := by rw [k2]; noncomm_ring
end PI.UnitaryApproxFinWork
