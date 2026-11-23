-- Prove2me | solution 1 for SecSampling.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T10:23:59.326313+00:00
-- url     : https://prove2.me/submissions/bdd08c63-3e55-4747-8f65-8eef49eec87b

import Mathlib
import Definitions.Def_SecSampling_AOSp
import Theorems.Thm_SecSampling_lemma_1
import Theorems.Thm_SecSampling_proposition_6
import Theorems.Thm_SecSampling_theorem_4

namespace NCSS
open SecSampling

/-- The instance used for the impossibility half: the first `m` elements have positive values
increasing in the index, the remaining ones negative values. -/
noncomputable def vals (m n : ℕ) (i : Fin n) : ℝ :=
  if (i : ℕ) < m then (i : ℝ) + 1 else -((i : ℝ) + 1)

lemma vals_injective (m n : ℕ) : Function.Injective (vals m n) := by
  intro i j h
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  apply Fin.ext
  unfold vals at h
  split_ifs at h <;> exact_mod_cast (by linarith : (i : ℝ) = j)

end NCSS

open SecSampling in
theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ (n : ℕ) (v : Fin n → ℝ), Function.Injective v →
      ∀ ord : Finset (Fin n) → List (Fin n), IsOnlineOrder ord →
        guarantee p ≤ winProb p (kmax p) v ord) ∧
    (∀ A : Algorithm, IsAlgorithm A → ∀ ε : ℝ, 0 < ε →
      ∃ (n : ℕ) (v : Fin n → ℝ), Function.Injective v ∧
        winProb p A v (indexOrder n) < guarantee p + ε) := by
  refine ⟨fun n v hv ord hord => ?_, fun A hA ε hε => ?_⟩
  · obtain ⟨h1, h2⟩ := lemma_1 p hp0 hp1
    by_cases hn : n ≤ kOf p
    · exact h1 n hn v hv ord hord
    · have := (h2 n (by omega) v hv).1 ord hord
      have : 0 ≤ p ^ n := pow_nonneg hp0.le n
      linarith
  · obtain ⟨B, hB, hBA⟩ := proposition_6 p hp0 hp1 A hA
    obtain ⟨m, n, -, hmn, hlt⟩ := theorem_4 p hp0 hp1 B hB ε hε 0
    refine ⟨n, NCSS.vals m n, NCSS.vals_injective m n, lt_of_le_of_lt ?_ hlt⟩
    refine hBA m n hmn _ (NCSS.vals_injective m n) ?_ ?_ ?_
    · intro i j hij hj
      have hi : (i : ℕ) < m := lt_trans hij hj
      simp only [NCSS.vals, if_pos hi, if_pos hj]
      have : (i : ℝ) < j := by exact_mod_cast hij
      linarith
    · intro i hi
      simp only [NCSS.vals, if_pos hi]
      positivity
    · intro i hi
      simp only [NCSS.vals, if_neg (not_lt.mpr hi)]
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg _
      linarith
