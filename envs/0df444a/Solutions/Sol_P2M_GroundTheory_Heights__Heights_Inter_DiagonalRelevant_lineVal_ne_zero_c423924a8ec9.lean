-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalRelevant_lineVal_ne_zero_c423924a8ec9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:59:25.895438+00:00
-- url     : https://prove2.me/submissions/30405b25-bbdf-44b0-b913-32e629e77b22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagRelevant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalRelevant
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalRelevant
theorem _root_.solution {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
    [Algebra Ω Φ] (e : Module.Basis (Fin 2) Ω E) {ψ : E →ₗ[Ω] Ω} (hψ : ψ ≠ 0) {a : Φ}
    (ha : Transcendental Ω a) : T.lineVal e ψ a ≠ 0 := by
  intro h
  unfold T.lineVal at h
  by_cases h1 : ψ (e 1) = 0
  · apply hψ
    refine e.ext fun q => ?_
    fin_cases q
    · simp only [h1, map_zero, mul_zero, add_zero] at h
      simpa using (map_eq_zero_iff _ (algebraMap Ω Φ).injective).1 h
    · simpa using h1
  · apply ha
    have h1' : algebraMap Ω Φ (ψ (e 1)) ≠ 0 := (map_ne_zero _).2 h1
    have : a = algebraMap Ω Φ (-(ψ (e 0)) / ψ (e 1)) := by
      rw [map_div₀, map_neg, eq_div_iff h1']
      linear_combination h
    rw [this]
    exact isAlgebraic_algebraMap _
end GroundTheory.Heights₂.Heights.Inter.DiagonalRelevant
