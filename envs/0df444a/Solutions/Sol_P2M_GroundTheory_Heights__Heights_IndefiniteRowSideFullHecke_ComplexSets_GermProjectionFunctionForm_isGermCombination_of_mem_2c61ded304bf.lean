-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermProjectionFunctionForm_isGermCombination_of_mem_2c61ded304bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:31:41.562126+00:00
-- url     : https://prove2.me/submissions/0c0b7fea-2a92-47f7-90f6-834ecde598e7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermProjectionFunctionForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermPrimitivePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermProjectionFunctionForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermPrimitivePresentation_exists_of_mem_holGermIdeal_6e04f02e5a02


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
open Topology Filter PrimeGermPrimitivePresentation
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GermProjectionFunctionForm
variable {σ : Type} [Fintype σ]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GermProjectionFunctionForm
theorem _root_.solution {w : σ → ℂ} {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) (u : anFun w)
    (hu : toGerm w u ∈ holGermIdeal w p) (f : (σ → ℂ) → ℂ) (hf : ∀ z, u.1 z = f z) :
    IsGermCombination w p f := by
  obtain ⟨h, hh, e⟩ := exists_of_mem_holGermIdeal p hu
  exact ⟨h, hh, (Germ.coe_eq.1 e).mono fun z hz => by rw [← hf]; exact hz⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GermProjectionFunctionForm
