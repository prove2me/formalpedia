-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.SmoothIntegrals.contDiffOn_integral_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:44:02.174753+00:00
-- url     : https://prove2.me/submissions/a102c219-7cfc-4b56-8d32-61d9cdbdddbc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PSmoothA
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_SmoothIntegrals_contDiffOn_pd
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_SmoothIntegrals_hasFDerivAt_step

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
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.CG.SmoothIntegrals
variable {X M T : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [TopologicalSpace T] [T2Space T] [MeasurableSpace T] [OpensMeasurableSpace T]
variable {μ : Measure T} [IsFiniteMeasureOnCompacts μ] {U : Set X} {W : Set M} {p : T → M}
namespace PositivityTheory.Rg.BcB.CG.SmoothIntegrals
theorem _root_.solution (hU : IsOpen U) (hW : IsOpen W) (hp : Continuous p) (hpW : ∀ y, p y ∈ W) (n : ℕ) :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : X × M → V),
      ContDiffOn ℝ ∞ Q (U ×ˢ W) → (∀ x ∈ U, ∃ K, IsCompact K ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ K, Q (x', p y) = 0) →
      ContDiffOn ℝ n (fun x => ∫ y, Q (x, p y) ∂μ) U := by
  induction n with
  | zero =>
    intro V _ _ _ Q hQ hs
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun x hx => (hasFDerivAt_step (μ := μ) hU hW hp hpW hQ hs hx).continuousAt.continuousWithinAt
  | succ n ih =>
    intro V _ _ _ Q hQ hs
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hasFDerivAt_step (μ := μ) hU hW hp hpW hQ hs hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have hs' : ∀ x ∈ U, ∃ K, IsCompact K ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ K, pd Q (x', p y) = 0 := by
      intro x hx
      obtain ⟨K, hK, hKe⟩ := hs x hx
      refine ⟨K, hK, ?_⟩
      filter_upwards [eventually_eventually_nhds.2 hKe] with x' hx' y hy
      have h0 : (fun x'' => Q (x'', p y)) =ᶠ[𝓝 x'] fun _ => 0 := hx'.mono fun x'' h => h y hy
      show fderiv ℝ (fun x'' => Q (x'', p y)) x' = 0
      rw [h0.fderiv_eq]
      exact fderiv_const_apply _
    exact (ih (X →L[ℝ] V) (pd Q) (contDiffOn_pd hU hW hQ) hs').congr fun x hx =>
      (hasFDerivAt_step (μ := μ) hU hW hp hpW hQ hs hx).fderiv
end PositivityTheory.Rg.BcB.CG.SmoothIntegrals
