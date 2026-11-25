-- Prove2me | solution 1 for PI.SqfRootsInj.W.cardB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:34:14.448786+00:00
-- url     : https://prove2.me/submissions/e40d1c66-b918-46ea-9d43-6ec322b839dc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_DivCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_TwoPowCardPrimeFactorsLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_CardLeSumOfCover
import Theorems.Thm_P2M_PI_SqfRootsInj_W_minpoly_monic__d5b12cc188a0
import Theorems.Thm_PI_SqfRootsInj_W_card_nthRoots_toFinset_le
import Theorems.Thm_PI_SqfRootsInj_W_card_roots_X_pow_sub_X_le
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
    (hmon : ∀ f ∈ T, f.Monic ∧ f.natDegree = r) : (T.filter (PB g r)).card ≤ SB g r := by
  have hg2 : 1 < g := hg.out.one_lt
  calc (T.filter (PB g r)).card ≤ ∑ e ∈ Finset.Icc 1 r, ∑ e' ∈ Finset.Icc 1 (min e (r - e)),
      ∑ ℓ ∈ LS g r ((g ^ e - 1) * (g ^ e' - 1)), ∑ y ∈ YB g e', ∑ x ∈ XB g e ℓ y,
        (T.filter (fun f => minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f)).card := by
        refine (Finset.card_le_card (t := (Finset.Icc 1 r).biUnion fun e =>
          (Finset.Icc 1 (min e (r - e))).biUnion fun e' => (LS g r ((g ^ e - 1) * (g ^ e' - 1))).biUnion fun ℓ =>
            (YB g e').biUnion fun y => (XB g e ℓ y).biUnion fun x =>
              T.filter (fun f => minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f)) ?_).trans ?_
        · intro f hf
          obtain ⟨hfT, e, he, e', he', ℓ, hℓ, y, hy, x, hx, hd⟩ := Finset.mem_filter.1 hf
          simp only [Finset.mem_biUnion]
          exact ⟨e, he, e', he', ℓ, hℓ, y, hy, x, hx, Finset.mem_filter.2 ⟨hfT, hd⟩⟩
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun e _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun e' _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun ℓ _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun y _ => ?_)
        exact Finset.card_biUnion_le
    _ ≤ SB g r := by
        refine Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun e' he' =>
          Finset.sum_le_sum fun ℓ _ => ?_
        have he1 : 1 ≤ e' := (Finset.mem_Icc.1 he').1
        calc ∑ y ∈ YB g e', ∑ x ∈ XB g e ℓ y,
              (T.filter (fun f => minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f)).card
            ≤ ∑ y ∈ YB g e', ∑ x ∈ XB g e ℓ y, g ^ (r - e - e') := by
              refine Finset.sum_le_sum fun y hy => Finset.sum_le_sum fun x hx => ?_
              have h1 := divCount r T hmon _ ((minpoly_monic' x).mul (minpoly_monic' y))
              have h2 : (minpoly (ZMod g) x * minpoly (ZMod g) y).natDegree = e + e' := by
                rw [(minpoly_monic' x).natDegree_mul (minpoly_monic' y),
                  (Finset.mem_filter.1 hx).2, (Finset.mem_filter.1 hy).2]
              rw [h2] at h1
              rw [Nat.sub_sub]
              exact h1
          _ = ∑ y ∈ YB g e', (XB g e ℓ y).card * g ^ (r - e - e') := by
              simp only [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ y ∈ YB g e', Lp g e ℓ * g ^ (r - e - e') :=
              Finset.sum_le_sum fun y _ => Nat.mul_le_mul_right _
                ((Finset.card_filter_le _ _).trans (card_nthRoots_toFinset_le _ _))
          _ = (YB g e').card * (Lp g e ℓ * g ^ (r - e - e')) := by
              rw [Finset.sum_const, smul_eq_mul]
          _ ≤ g ^ e' * (Lp g e ℓ * g ^ (r - e - e')) :=
              Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans
                (card_roots_X_pow_sub_X_le _ (Nat.one_lt_pow (by omega) hg2)))
          _ = g ^ e' * Lp g e ℓ * g ^ (r - e - e') := by rw [mul_assoc]
end PI.SqfRootsInj.W
