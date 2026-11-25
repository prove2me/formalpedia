-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Holtb.differentiableOn_integral_of_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:41.001232+00:00
-- url     : https://prove2.me/submissions/80cfd417-db20-47ac-8e07-2f922d49cb0c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_HolomorphicTheta_IntHol
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Holtb_aesm_fderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric Set
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Holtb
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
namespace PositivityTheory.SiegelWeilFormula.Holtb
theorem _root_.solution [IsFiniteMeasure ν] {U : Set E} (hU : IsOpen U) (f : X → E → ℂ)
    (hd : ∀ x, DifferentiableOn ℂ (f x) U) (hm : ∀ W ∈ U, AEStronglyMeasurable (f · W) ν)
    (hb : ∀ W₀ ∈ U, ∃ r > 0, ∃ M, ball W₀ r ⊆ U ∧ ∀ x, ∀ W ∈ ball W₀ r, ‖f x W‖ ≤ M) :
    DifferentiableOn ℂ (fun W => ∫ x, f x W ∂ν) U := by
  intro W₀ hW₀
  obtain ⟨r, hr, M, hsub, hM⟩ := hb W₀ hW₀
  set M' := max M 0
  have hM' : ∀ x, ∀ W ∈ ball W₀ r, ‖f x W‖ ≤ M' := fun x W hW => (hM x W hW).trans (le_max_left _ _)
  have hdiffAt : ∀ x, ∀ W ∈ ball W₀ r, DifferentiableAt ℂ (f x) W := fun x W hW =>
    (hd x).differentiableAt (hU.mem_nhds (hsub hW))
  have hball : ∀ W ∈ ball W₀ (r / 2), ball W (r / 2) ⊆ ball W₀ r := by
    intro W hW
    apply ball_subset_ball'
    rw [mem_ball] at hW
    linarith
  have hbnd : ∀ x, ∀ W ∈ ball W₀ (r / 2), ‖fderiv ℂ (f x) W‖ ≤ (2 * M') / (r / 2) := by
    intro x W hW
    apply Complex.norm_fderiv_le_div_of_mapsTo_ball
    · exact (hd x).mono ((hball W hW).trans hsub)
    · intro Z hZ
      rw [mem_closedBall, dist_eq_norm]
      have hZ' : Z ∈ ball W₀ r := hball W hW hZ
      have hW' : W ∈ ball W₀ r := ball_subset_ball (by linarith) hW
      calc ‖f x Z - f x W‖ ≤ ‖f x Z‖ + ‖f x W‖ := norm_sub_le _ _
        _ ≤ M' + M' := add_le_add (hM' x Z hZ') (hM' x W hW')
        _ = 2 * M' := by ring
    · positivity
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := fun W x => f x W)
    (F' := fun W x => fderiv ℂ (f x) W) (bound := fun _ => (2 * M') / (r / 2)) (s := ball W₀ (r / 2)) (x₀ := W₀)
    (ball_mem_nhds W₀ (by positivity))
    (eventually_of_mem (hU.mem_nhds hW₀) fun W hW => hm W hW)
    ((integrable_const M').mono' (hm W₀ hW₀) (ae_of_all _ fun x => hM' x W₀ (mem_ball_self hr)))
    (aesm_fderiv f W₀ r hr (fun x => hdiffAt x W₀ (mem_ball_self hr)) (fun W hW => hm W (hsub hW)))
    (ae_of_all _ fun x W hW => hbnd x W hW)
    (integrable_const _)
    (ae_of_all _ fun x W hW => (hdiffAt x W (ball_subset_ball (by linarith) hW)).hasFDerivAt)
  exact key.differentiableAt.differentiableWithinAt
end PositivityTheory.SiegelWeilFormula.Holtb
