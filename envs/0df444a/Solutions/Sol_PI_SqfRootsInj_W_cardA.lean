-- Prove2me | solution 1 for PI.SqfRootsInj.W.cardA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:52.444686+00:00
-- url     : https://prove2.me/submissions/669027bb-039e-4b59-95b9-9358b0b3badc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_DivCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_TwoPowCardPrimeFactorsLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_CardLeSumOfCover
import Theorems.Thm_P2M_PI_SqfRootsInj_W_minpoly_monic__d5b12cc188a0
import Theorems.Thm_PI_SqfRootsInj_W_card_nthRoots_toFinset_le
import Theorems.Thm_PI_SqfRootsInj_W_divCount


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
    (hmon : ∀ f ∈ T, f.Monic ∧ f.natDegree = r) : (T.filter (PA g r)).card ≤ SA g r := by
  calc (T.filter (PA g r)).card ≤ ∑ e ∈ Finset.Icc 2 r, ∑ j ∈ Finset.Icc 1 (e / 2),
      ∑ ℓ ∈ LS g r (g ^ e - 1), ∑ w ∈ WA g e j ℓ,
        (T.filter (fun f => minpoly (ZMod g) w ∣ f)).card := by
        refine (Finset.card_le_card (t := (Finset.Icc 2 r).biUnion fun e =>
          (Finset.Icc 1 (e / 2)).biUnion fun j => (LS g r (g ^ e - 1)).biUnion fun ℓ =>
            (WA g e j ℓ).biUnion fun w => T.filter (fun f => minpoly (ZMod g) w ∣ f)) ?_).trans ?_
        · intro f hf
          obtain ⟨hfT, e, he, j, hj, ℓ, hℓ, w, hw, hd⟩ := Finset.mem_filter.1 hf
          simp only [Finset.mem_biUnion]
          exact ⟨e, he, j, hj, ℓ, hℓ, w, hw, Finset.mem_filter.2 ⟨hfT, hd⟩⟩
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun e _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun ℓ _ => ?_)
        exact Finset.card_biUnion_le
    _ ≤ SA g r := by
        refine Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun ℓ _ => ?_
        calc ∑ w ∈ WA g e j ℓ, (T.filter (fun f => minpoly (ZMod g) w ∣ f)).card
            ≤ ∑ w ∈ WA g e j ℓ, g ^ (r - e) := by
              refine Finset.sum_le_sum fun w hw => ?_
              have h1 := divCount r T hmon _ (minpoly_monic' w)
              have h2 : (minpoly (ZMod g) w).natDegree = e := (Finset.mem_filter.1 hw).2
              rw [h2] at h1
              exact h1
          _ = (WA g e j ℓ).card * g ^ (r - e) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ (g ^ j - 1) * Lp g e ℓ * g ^ (r - e) :=
              Nat.mul_le_mul_right _
                ((Finset.card_filter_le _ _).trans (card_nthRoots_toFinset_le _ _))
end PI.SqfRootsInj.W
