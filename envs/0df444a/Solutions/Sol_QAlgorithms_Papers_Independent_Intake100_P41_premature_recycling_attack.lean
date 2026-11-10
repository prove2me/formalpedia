-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P41.premature_recycling_attack
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T03:29:23.298332+00:00
-- url     : https://prove2.me/submissions/9f7dbd32-247d-409c-82d1-d1e409667b16

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P41

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Aux_P41_pra

theorem filter_all_div {S : Type*} [Fintype S] [Nonempty S] (p : S → Prop)
    {inst : DecidablePred p} (hp : ∀ s, p s) :
    ((@Finset.filter S p inst Finset.univ).card : ℝ) / (Fintype.card S : ℝ) = 1 := by
  rw [@Finset.filter_true_of_mem S p inst Finset.univ (fun s _ => hp s), Finset.card_univ]
  exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

end Aux_P41_pra

open QAlgorithms.Papers.Independent.Intake100.P41
  QAlgorithms.Papers.Independent.Bridge50.P44 in
theorem solution {K X : Type*} [Fintype K] [Nonempty K]
    {m : ℕ} (h : K → X → Tag m) (x xprime : X) (hne : x ≠ xprime) :
    ∃ a : K → X × Tag m → X × Tag m,
      uniformProbability (fun seed : K × Tag m =>
        let view := (prematureReleaseView h a seed.1 seed.2 x).2
        view.submitted.1 = xprime ∧ view.accepted = true) = 1 := by
  have key : ∀ (k : K) (pad : Tag m),
      xorWord (h k xprime) (xorWord (h k x) (xorWord (h k x) pad)) = xorWord (h k xprime) pad := by
    intro k pad
    funext i
    simp only [xorWord]
    cases h k xprime i <;> cases h k x i <;> cases pad i <;> rfl
  refine ⟨fun k p => (xprime, xorWord (h k xprime) (xorWord (h k p.1) p.2)), ?_⟩
  unfold uniformProbability
  refine Aux_P41_pra.filter_all_div _ (fun seed => ?_)
  · refine ⟨rfl, ?_⟩
    show decide (_ = _) = true
    rw [decide_eq_true_iff]
    exact key seed.1 seed.2
