-- Prove2me | solution 1 for P2M_GlobalTheory_RealWeil_hasTemperateGrowth_phase__6de2e378a47e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:41:46.55678+00:00
-- url     : https://prove2.me/submissions/98d4a6ea-5401-47ba-83b6-bed7a2f16471

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Theorems.Thm_GlobalTheory_RealWeil_phase_eq_eChar
import Theorems.Thm_GlobalTheory_Published_Metaplectic_hasTemperateGrowth_eChar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
namespace GlobalTheory.RealWeil
theorem _root_.solution (w : l ⊕ l → ℝ) : Function.HasTemperateGrowth (phase w) := by
  have h1 : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => ⟪qPart w, x⟫ :=
    (innerSL ℝ (qPart w)).hasTemperateGrowth
  have h := GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp (h1.add (Function.HasTemperateGrowth.const
    (⟪pPart w, qPart w⟫ / 2)))
  have e : phase w = (GlobalTheory.Published.Metaplectic.eChar : ℝ → ℂ) ∘
      ((fun x : EuclideanSpace ℝ l => ⟪qPart w, x⟫) + fun _ => ⟪pPart w, qPart w⟫ / 2) := by
    funext x
    simp [phase_eq_eChar]
  rw [e]
  exact h
end GlobalTheory.RealWeil
