-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_analyticAt_of_holoOn_c7b3bffc3f2a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:32:14.720097+00:00
-- url     : https://prove2.me/submissions/e0ceb887-ad55-4f68-b6fa-cdb179819caa

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
theorem _root_.solution (A : FinHolAtlas D U) {f : U → ℂ} {c : Fin A.n}
    (hf : A.HoloOn (A.chart c).source f) {x : U} (hx : x ∈ (A.chart c).source) :
    AnalyticAt ℂ (f ∘ (A.chart c).symm) (A.chart c x) :=
  hf c _ ⟨(A.chart c).map_source hx, by rw [Set.mem_preimage, (A.chart c).left_inv hx]; exact hx⟩
end GroundTheory.Heights₂.Heights.EffectiveHS.EffectiveHilbertSamuelJetLemmas
