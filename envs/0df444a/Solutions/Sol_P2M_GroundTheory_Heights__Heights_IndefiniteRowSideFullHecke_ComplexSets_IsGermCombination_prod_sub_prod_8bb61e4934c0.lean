-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsGermCombination_prod_sub_prod_8bb61e4934c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:31:46.330824+00:00
-- url     : https://prove2.me/submissions/daaa140c-0d98-43f3-8e1d-7bb8eea4c222

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PevEqZeroOfPresentation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsGermCombination_zero_5b85769bc1a2

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
open Topology Filter Polynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsGermCombination
variable {σ : Type} [Fintype σ] {w : σ → ℂ} {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsGermCombination
theorem _root_.solution {ι : Type*} (s : Finset ι) {f g : ι → (σ → ℂ) → ℂ}
    (hf : ∀ i, AnalyticAt ℂ (f i) w) (hg : ∀ i, AnalyticAt ℂ (g i) w)
    (h : ∀ i, IsGermCombination w p (fun z => f i z - g i z)) :
    IsGermCombination w p (fun z => ∏ i ∈ s, f i z - ∏ i ∈ s, g i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact zero.congr (Eventually.of_forall fun z => by simp)
  | insert a s ha ih =>
    have hgs : AnalyticAt ℂ (fun z => ∏ i ∈ s, g i z) w := Finset.analyticAt_fun_prod s fun i _ => hg i
    exact ((mul_left (hf a) ih).add (mul_left hgs (h a))).congr
      (Eventually.of_forall fun z => by rw [Finset.prod_insert ha, Finset.prod_insert ha]; ring)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsGermCombination
