-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_chart_sum_eq_8fb30277a532
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:32:18.60213+00:00
-- url     : https://prove2.me/submissions/69984773-db72-487c-b16b-31ef2058b44c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_SymbolExtensionProperty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_MemSectionsOfHolLineBundleEquiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_JetOfMonomialSumStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_AnalyticAtOfHoloOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.EffectiveHS
open ReciprocityTheory.AnForm.M
noncomputable section
open GroundTheory.Heights₂.Heights.EffectiveHS.EffectiveHilbertSamuelJetLemmas
variable {D : ℕ} {U : Type} [TopologicalSpace U]
namespace GroundTheory.Heights₂.Heights.EffectiveHS.EffectiveHilbertSamuelJetLemmas
theorem _root_.solution (A : FinHolAtlas D U) (s : Fin D → Fin A.n → U → ℂ) (a : ℕ)
    (h : (Fin D → ℕ) → Fin A.n → U → ℂ) (c : Fin A.n) :
    (∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow s α * h α) c ∘ (A.chart c).symm =
      fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple D a,
        (∏ i, (s i c ∘ (A.chart c).symm) z ^ α i) * (h α c ∘ (A.chart c).symm) z := by
  funext z
  simp [sPow, Finset.sum_apply, Finset.prod_apply]
end GroundTheory.Heights₂.Heights.EffectiveHS.EffectiveHilbertSamuelJetLemmas
