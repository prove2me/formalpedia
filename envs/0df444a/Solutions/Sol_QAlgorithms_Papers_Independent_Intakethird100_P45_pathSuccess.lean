-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P45.pathSuccess
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:12:20.609217+00:00
-- url     : https://prove2.me/submissions/a3e0f111-55fa-4c20-8f67-74819b13461d

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P45

open scoped BigOperators

noncomputable section

open QAlgorithms.Papers.Independent.Intakethird100.P45 in
theorem solution (k : ℕ) (hk : 0 < k) (p q : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    chainProbability k p q = p ^ k * q ^ (k - 1) := by
  suffices hmain : (∑ e : Fin k → Bool, ∑ f : Fin (k - 1) → Bool,
      if (∀ i, e i = true) ∧ (∀ j, f j = true) then iidMass p e * iidMass q f else 0)
      = p ^ k * q ^ (k - 1) by
    unfold chainProbability
    convert hmain
  rw [Finset.sum_eq_single (fun _ => true)]
  · rw [Finset.sum_eq_single (fun _ => true)]
    · rw [if_pos ⟨fun _ => rfl, fun _ => rfl⟩]
      simp [iidMass]
    · intro f _ hf
      rw [if_neg]
      rintro ⟨-, h⟩
      exact hf (funext h)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro e _ he
    apply Finset.sum_eq_zero
    intro f _
    rw [if_neg]
    rintro ⟨h, -⟩
    exact he (funext h)
  · intro h
    exact absurd (Finset.mem_univ _) h

end
