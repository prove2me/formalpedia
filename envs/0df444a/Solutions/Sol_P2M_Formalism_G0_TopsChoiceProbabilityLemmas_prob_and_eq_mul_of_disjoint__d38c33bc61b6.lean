-- Prove2me | solution 1 for P2M_Formalism_G0_TopsChoiceProbabilityLemmas_prob_and_eq_mul_of_disjoint__d38c33bc61b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:15.920148+00:00
-- url     : https://prove2.me/submissions/d6146a29-93a3-4e9e-bd84-5e51e350691e

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_and_eq_mul_of_disjoint
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_eq_of_dependsOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsChoiceProbabilityLemmas
open TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsChoiceProbabilityLemmas
theorem _root_.solution {U S R : Finset ℕ} (δ : ℝ) (hS : S ⊆ U) (hR : R ⊆ U) (h : Disjoint S R)
    {A B : Finset ℕ → Prop} (hA : Dep S A) (hB : Dep R B) :
    P U δ (fun t => A t ∧ B t) = P U δ A * P U δ B := by
  have hD : Dep (S ∪ R) (fun t => A t ∧ B t) := by
    intro t
    have e1 : t ∩ (S ∪ R) ∩ S = t ∩ S := by rw [inter_assoc, inter_eq_right.2 subset_union_left]
    have e2 : t ∩ (S ∪ R) ∩ R = t ∩ R := by rw [inter_assoc, inter_eq_right.2 subset_union_right]
    show A t ∧ B t ↔ A (t ∩ (S ∪ R)) ∧ B (t ∩ (S ∪ R))
    rw [hA (t ∩ (S ∪ R)), hB (t ∩ (S ∪ R)), e1, e2]
    exact and_congr (hA t) (hB t)
  rw [prob_eq_of_dependsOn δ (union_subset hS hR) hD, prob_eq_of_dependsOn δ hS hA, prob_eq_of_dependsOn δ hR hB, ← prob_and_eq_mul_of_disjoint S R δ h]
  congr 1
  funext t
  exact propext (and_congr (hA t) (hB t))
end Formalism.G0.TopsChoiceProbabilityLemmas
