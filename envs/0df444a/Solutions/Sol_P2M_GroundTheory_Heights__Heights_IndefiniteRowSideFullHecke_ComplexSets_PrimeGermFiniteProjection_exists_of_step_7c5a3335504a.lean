-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermFiniteProjection_exists_of_step_7c5a3335504a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:09:03.37213+00:00
-- url     : https://prove2.me/submissions/b3cbeec7-7315-4e63-8ccb-2800466ea359

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermFiniteProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermProjectionFunctionForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermProjectionStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermFiniteProjection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isFiniteGermProjection_bot_d24e95e81a5c


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
open Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace PrimeGermFiniteProjection
theorem _root_.solution (hStep : PrimeGermProjectionStep.Statement) :
    ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (P : Ideal (holGerms w)), P.IsPrime →
      ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w P A := by
  have key : ∀ (n : ℕ) (σ : Type) [Fintype σ], Fintype.card σ = n → ∀ (w : σ → ℂ) (P : Ideal (holGerms w)),
      P.IsPrime → ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w P A := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro σ _ hn w P hP
      by_cases h0 : P = ⊥
      · subst h0
        exact isFiniteGermProjection_bot w
      · exact hStep σ w P hP h0 fun τ _ hτ v Q hQ => ih _ (hn ▸ hτ) τ rfl v Q hQ
  intro σ _ w P hP
  exact key _ σ rfl w P hP
end PrimeGermFiniteProjection
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
