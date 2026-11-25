-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_eval_ne_zero_of_isOpen_6ffa7e418c93
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:56:40.442381+00:00
-- url     : https://prove2.me/submissions/b4a739b8-4564-48a0-91c1-3c7655ddbc0b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZeroSetOpenMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PZeroSetOpenMass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial MeasureTheory Filter Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {d : ℕ} {P : MvPolynomial (Fin d) ℂ} (hP : P ≠ 0)
    {S : Set (Fin d → ℂ)} (hS : IsOpen S) (hne : S.Nonempty) : ∃ y ∈ S, eval y P ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hS y₀ hy₀
  by_contra h
  push Not at h
  apply hP
  have hinf : ∀ i, (Metric.ball (y₀ i) r).Infinite := fun i =>
    infinite_of_mem_nhds (y₀ i) (Metric.ball_mem_nhds _ hr)
  refine (funext_set_iff (p := P) (q := 0) _ hinf).mpr fun y hy => ?_
  rw [map_zero]
  exact h y (hball (by rwa [ball_pi _ hr]))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
