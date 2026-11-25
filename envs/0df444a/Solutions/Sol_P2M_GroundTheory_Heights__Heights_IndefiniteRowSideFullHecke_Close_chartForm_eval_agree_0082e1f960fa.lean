-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_chartForm_eval_agree_0082e1f960fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:56:17.334892+00:00
-- url     : https://prove2.me/submissions/a5ccf9f9-f49c-4691-9ff9-d2ea38b5d609

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ChartFormEvalAgree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (P : ArithVariety n) (A A' : HermLine n) (hdeg : A'.deg = A.deg)
    (hmet : ∀ z ∈ P.points ℂ, A'.metric z = A.metric z)
    (h : ∀ s : IntegralSection P A'.deg,
      (∀ z ∈ P.points ℂ, ∀ (c c' : (k : ι) → Fin (n k + 1)) (d d' : ι → ℕ)
          (e e' : MvPolynomial (Coord n) ℤ),
        IsChartForm P A'.deg s.num s.den c d e → IsChartForm P A'.deg s.num s.den c' d' e' →
        (∀ k, z k (c k) ≠ 0) → (∀ k, z k (c' k) ≠ 0) →
          ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * A'.metric z) =
            ‖evalCone z e'‖ / (‖evalCone z (chartMonomial c' d')‖ * A'.metric z)) ∧
        ∃ C : ℝ, s.SupNormLE A' C)
    (s : IntegralSection P A.deg) :
    (∀ z ∈ P.points ℂ, ∀ (c c' : (k : ι) → Fin (n k + 1)) (d d' : ι → ℕ)
        (e e' : MvPolynomial (Coord n) ℤ),
      IsChartForm P A.deg s.num s.den c d e → IsChartForm P A.deg s.num s.den c' d' e' →
      (∀ k, z k (c k) ≠ 0) → (∀ k, z k (c' k) ≠ 0) →
        ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * A.metric z) =
          ‖evalCone z e'‖ / (‖evalCone z (chartMonomial c' d')‖ * A.metric z)) ∧
      ∃ C : ℝ, s.SupNormLE A C := by
  obtain ⟨deg, metric, h1, h2, h3⟩ := A'
  dsimp only at hdeg hmet h
  subst hdeg
  obtain ⟨hind, C, hC⟩ := h s
  refine ⟨fun z hz c c' d d' e e' he he' hc hc' ↦ ?_, C, fun z hz c d e he hc ↦ ?_⟩
  · rw [← hmet z hz]
    exact hind z hz c c' d d' e e' he he' hc hc'
  · rw [← hmet z hz]
    exact hC z hz c d e he hc
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
