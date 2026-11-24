-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_eval_ne_zero_of_isOpen_a58e4a73048f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:27.792526+00:00
-- url     : https://prove2.me/submissions/a8c80634-78d8-4aeb-9c65-d565b57196fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StGrowthOffHypersurfacePolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StEntirePolynomialGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PGrowthOffHypersurfacePolynomial

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {d : ℕ} {Q : MvPolynomial (Fin d) ℂ} (hQ : Q ≠ 0)
    {V : Set (Fin d → ℂ)} (hV : IsOpen V) (hne : V.Nonempty) : ∃ t ∈ V, eval t Q ≠ 0 := by
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  obtain ⟨t, ht⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV t ht
  apply hQ
  refine MvPolynomial.funext_set (fun i => Metric.ball (t i) ε) (fun i => ?_) (fun x hx => ?_)
  · exact infinite_of_mem_nhds (t i) (Metric.ball_mem_nhds (t i) hε)
  · rw [map_zero]
    apply hall
    apply hball
    rw [ball_pi t hε]
    exact hx
end GroundTheory.Heights₂.Heights.HilbertSamuel
