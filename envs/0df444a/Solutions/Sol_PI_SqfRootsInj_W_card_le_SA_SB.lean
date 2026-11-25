-- Prove2me | solution 1 for PI.SqfRootsInj.W.card_le_SA_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:30.714706+00:00
-- url     : https://prove2.me/submissions/f00afef3-bf10-4c27-aa63-09f517fa2b46

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_DivCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_TwoPowCardPrimeFactorsLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_CardLeSumOfCover
import Theorems.Thm_PI_SqfRootsInj_W_caseA_PA
import Theorems.Thm_PI_SqfRootsInj_W_caseB_PB
import Theorems.Thm_PI_SqfRootsInj_W_cardA
import Theorems.Thm_PI_SqfRootsInj_W_cardB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
namespace PI.SqfRootsInj.W
theorem _root_.solution (g r : ℕ) [hg : Fact g.Prime] (T : Finset (ZMod g)[X])
    (hT : ∀ f ∈ T, IsLab g r f ∧ ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ BB r g ∧
      (CaseA g r ℓ f ∨ CaseB g r ℓ f)) :
    T.card ≤ SA g r + SB g r := by
  have hmon : ∀ f ∈ T, f.Monic ∧ f.natDegree = r := fun f hf => ⟨(hT f hf).1.1, (hT f hf).1.2.1⟩
  have hcov : T ⊆ T.filter (PA g r) ∪ T.filter (PB g r) := by
    intro f hf
    obtain ⟨_, ℓ, hℓ, hB, hAB⟩ := hT f hf
    rcases hAB with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hf, caseA_PA hℓ hB h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hf, caseB_PB hℓ hB h⟩)
  calc T.card ≤ (T.filter (PA g r) ∪ T.filter (PB g r)).card := Finset.card_le_card hcov
    _ ≤ (T.filter (PA g r)).card + (T.filter (PB g r)).card := Finset.card_union_le _ _
    _ ≤ SA g r + SB g r := Nat.add_le_add (cardA g r T hmon) (cardB g r T hmon)
end PI.SqfRootsInj.W
