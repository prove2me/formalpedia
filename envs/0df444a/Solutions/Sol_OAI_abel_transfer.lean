-- Prove2me | solution 1 for OAI.abel_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:29:39.440831+00:00
-- url     : https://prove2.me/submissions/014e353b-5fec-41be-b34c-ef2f1f59f43e

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
namespace OAI
theorem _root_.solution (P V W : ℝ → ℂ) (p w : ℂ)
    (hP : Tendsto P (𝓝[>] (0 : ℝ)) (𝓝 p))
    (hW : Tendsto (fun η : ℝ => (η : ℂ) * W η) (𝓝[>] (0 : ℝ)) (𝓝 w))
    (hE : Tendsto (fun η => η * ‖V η - W η‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    Tendsto (fun η : ℝ => (η : ℂ) * (P η * V η))
      (𝓝[>] (0 : ℝ)) (𝓝 (p * w)) := by
  have hdiff : Tendsto (fun η : ℝ => (η : ℂ) * (V η - W η))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have heq : (fun η : ℝ => ‖(η : ℂ) * (V η - W η)‖) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun η => η * ‖V η - W η‖) := by
      filter_upwards [self_mem_nhdsWithin] with η hη
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
    exact hE.congr' heq.symm
  have hV : Tendsto (fun η : ℝ => (η : ℂ) * V η)
      (𝓝[>] (0 : ℝ)) (𝓝 w) := by
    convert hW.add hdiff using 1
    · funext η; ring
    · simp
  convert hP.mul hV using 1
  · funext η; ring
end OAI
