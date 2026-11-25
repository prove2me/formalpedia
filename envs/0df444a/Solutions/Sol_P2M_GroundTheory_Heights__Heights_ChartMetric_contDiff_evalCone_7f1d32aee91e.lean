-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMetric_contDiff_evalCone_7f1d32aee91e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:45.349795+00:00
-- url     : https://prove2.me/submissions/07802e59-9c96-4c1d-bc56-52948d18fe04

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_NormSqEvalConeScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMetric
namespace GroundTheory.Heights₂.Heights.ChartMetric
theorem _root_.solution {ι : Type} [Fintype ι] {n : ι → ℕ} (f : MvPolynomial (Coord n) ℤ) :
    ContDiff ℝ ∞ (fun z : Cone n ℂ ↦ evalCone z f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h : (fun z : Cone n ℂ ↦ evalCone z (C a)) = fun _ ↦ (a : ℂ) := by
      funext z; unfold evalCone; rw [eval₂_C]; simp
    rw [h]; exact contDiff_const
  | add p q hp hq =>
    have h : (fun z : Cone n ℂ ↦ evalCone z (p + q)) = fun z ↦ evalCone z p + evalCone z q := by
      funext z; simp [evalCone, eval₂_add]
    rw [h]; exact hp.add hq
  | mul_X p v hp =>
    have h : (fun z : Cone n ℂ ↦ evalCone z (p * X v)) = fun z ↦ evalCone z p * z v.1 v.2 := by
      funext z; simp [evalCone, eval₂_mul, eval₂_X]
    have hv : ContDiff ℝ ∞ (fun z : Cone n ℂ ↦ z v.1 v.2) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n v.1 + 1) ↦ ℂ) v.2).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun k ↦ Fin (n k + 1) → ℂ) v.1)).contDiff
    rw [h]; exact hp.mul hv
end GroundTheory.Heights₂.Heights.ChartMetric
