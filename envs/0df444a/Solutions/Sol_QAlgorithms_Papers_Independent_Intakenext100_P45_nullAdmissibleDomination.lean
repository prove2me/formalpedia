-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P45.nullAdmissibleDomination
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T01:47:07.203882+00:00
-- url     : https://prove2.me/submissions/49221df5-08f7-4569-8e05-c32a76f9b1b2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P45

noncomputable section

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal BigOperators Topology

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

open QAlgorithms.Papers.Independent.Intakenext100.P45 in
theorem solution (p q : I → ℝ) (hp : IsLaw p) (hq : IsLaw q) (n : ℕ) (hn : 0 < n)
    (f : ObservableWords p q n → Bool) :
    ∃ g : ObservableWords p q n → Bool, NullAdmissible p q g ∧
      observableAlpha p q g ≤ observableAlpha p q f ∧
      observableBeta p q g ≤ observableBeta p q f := by
  have hpn : ∀ x : Fin n → I, 0 ≤ iidLaw p n x := fun x =>
    Finset.prod_nonneg (fun j _ => hp.1 (x j))
  have hqn : ∀ x : Fin n → I, 0 ≤ iidLaw q n x := fun x =>
    Finset.prod_nonneg (fun j _ => hq.1 (x j))
  refine ⟨fun x => if iidLaw q n x.1 = 0 then false else
    if iidLaw p n x.1 = 0 then true else f x, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hq0
      dsimp only
      rw [if_pos hq0]
    · intro hp0
      have hq0 : iidLaw q n x.1 ≠ 0 := by
        intro hq0
        rcases x.2 with h | h
        · rw [hp0] at h; exact lt_irrefl _ h
        · rw [hq0] at h; exact lt_irrefl _ h
      dsimp only
      rw [if_neg hq0, if_pos hp0]
  · unfold observableAlpha
    apply Finset.sum_le_sum
    intro x _
    by_cases hq0 : iidLaw q n x.1 = 0
    · simp only [if_pos hq0, Bool.false_eq_true, if_false]
      split_ifs
      · exact hpn _
      · exact le_rfl
    · by_cases hp0 : iidLaw p n x.1 = 0
      · simp only [if_neg hq0, if_pos hp0, eq_self_iff_true, if_true, hp0]
        split_ifs
        · exact le_rfl
        · exact le_rfl
      · simp only [if_neg hq0, if_neg hp0, le_refl]
  · unfold observableBeta
    apply Finset.sum_le_sum
    intro x _
    by_cases hq0 : iidLaw q n x.1 = 0
    · simp only [if_pos hq0, Bool.false_eq_true, if_false, hq0]
      split_ifs <;> first | exact le_rfl | exact hqn _ | simp_all
    · by_cases hp0 : iidLaw p n x.1 = 0
      · simp only [if_neg hq0, if_pos hp0, eq_self_iff_true, if_true]
        split_ifs
        · exact le_rfl
        · exact hqn _
      · simp only [if_neg hq0, if_neg hp0, le_refl]

end
