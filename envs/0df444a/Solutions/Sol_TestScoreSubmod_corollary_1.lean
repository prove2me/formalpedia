-- Prove2me | solution 1 for TestScoreSubmod.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:29:20.449195+00:00
-- url     : https://prove2.me/submissions/6fec48e7-280d-41ba-9711-a6321d30699f

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_TestScoreSubmod_IsTopK
import Definitions.Def_TestScoreSubmod_IsGoodScores

open TestScoreSubmod in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (u : Finset ι → ℝ) (a : ι → ℝ)
    (p q : ℝ) (k : ℕ) (hk : 0 < k)
    (hu0 : ∀ S, 0 ≤ u S) (humono : Monotone u) (husub : NonmonotoneSubmod.Shared.Submodular u)
    (hp : 0 < p) (hq : 0 ≤ q) (hgood : IsGoodScores k p q a u)
    (S : Finset ι) (hS : IsTopK a k S) :
    ∀ T : Finset ι, T.card = k → p / (p + q) * u T ≤ u S := by
  intro T hT
  have hpq : 0 < p + q := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hpq]
  by_cases hne : (T \ S).Nonempty
  · have hSne : S.Nonempty := Finset.card_pos.mp (hS.1 ▸ hk)
    have h1 : u T ≤ u S + u (T \ S) := by
      have := husub S (T \ S)
      rw [Finset.union_sdiff_self_eq_union] at this
      have h2 : u T ≤ u (S ∪ T) := humono Finset.subset_union_right
      linarith [hu0 (S ∩ (T \ S))]
    have h3 : u (T \ S) ≤ q * (T \ S).sup' hne a :=
      hgood.2 _ hne (le_trans (Finset.card_le_card Finset.sdiff_subset) hT.le)
    have h4 : (T \ S).sup' hne a ≤ S.inf' hSne a := by
      apply Finset.sup'_le
      intro j hj
      apply Finset.le_inf'
      intro i hi
      exact hS.2 i hi j (Finset.mem_sdiff.mp hj).2
    have h5 : p * S.inf' hSne a ≤ u S := hgood.1 S hSne hS.1
    have h6 : p * u (T \ S) ≤ q * u S := by
      calc p * u (T \ S) ≤ p * (q * (T \ S).sup' hne a) := mul_le_mul_of_nonneg_left h3 hp.le
        _ ≤ p * (q * S.inf' hSne a) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hq) hp.le
        _ = q * (p * S.inf' hSne a) := by ring
        _ ≤ q * u S := mul_le_mul_of_nonneg_left h5 hq
    nlinarith
  · have hsub : T ⊆ S := by
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hne
      exact hne
    have := humono hsub
    nlinarith [hu0 T, hu0 S]
