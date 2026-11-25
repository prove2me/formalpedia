-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_dense_ne_zero_1de0df4f6e8a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:52.102474+00:00
-- url     : https://prove2.me/submissions/f8fcb4b8-9e70-4587-b573-0d46600c0540

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_BasicOpenSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Filter Topology
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace IrreducibleBasicOpenConnected
theorem _root_.solution {d : ℕ} {R : MvPolynomial (Fin d) ℂ} (hR : R ≠ 0) :
    Dense {y : Fin d → ℂ | eval y R ≠ 0} := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨y₀, hy₀⟩
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y₀ hy₀
  apply hR
  refine funext_set (fun j => Metric.ball (y₀ j) ε)
    (fun j => infinite_of_mem_nhds (y₀ j) (Metric.ball_mem_nhds _ hε)) fun y hy => ?_
  rw [← ball_pi y₀ hε] at hy
  rw [map_zero]
  by_contra hyR
  exact (Set.eq_empty_iff_forall_notMem.mp hne) y ⟨hball hy, hyR⟩
end IrreducibleBasicOpenConnected
end GroundTheory.Heights₂.Heights.HilbertSamuel
