-- Prove2me | solution 1 for Supermodularity.Cooperative.greedy_partial_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T06:52:51.067428+00:00
-- url     : https://prove2.me/submissions/18082c40-c0e1-4366-9266-d42db73bd421

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_IsConvexGame
import Definitions.Def_Supermodularity_Cooperative_InitialCoalition
import Definitions.Def_Supermodularity_Cooperative_GreedyPayoff

set_option autoImplicit false

open Supermodularity.Cooperative in
theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (hf : IsConvexGame f)
    (σ : Equiv.Perm (Fin n)) (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    ∑ i ∈ InitialCoalition σ j, GreedyPayoff σ f i = f (InitialCoalition σ j) := by
  clear hj1 hjn
  induction j with
  | zero =>
    have h0 : InitialCoalition σ 0 = ∅ := by
      ext k
      simp [InitialCoalition]
    rw [h0, Finset.sum_empty, hf.1]
  | succ j ih =>
    by_cases hj : j < n
    · have hmem : σ ⟨j, hj⟩ ∉ InitialCoalition σ j := by
        simp [InitialCoalition]
      have hins : InitialCoalition σ (j + 1) = insert (σ ⟨j, hj⟩) (InitialCoalition σ j) := by
        ext k
        simp only [InitialCoalition, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert]
        constructor
        · intro hk
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
          · exact Or.inr h
          · left
            have hk' : σ.symm k = ⟨j, hj⟩ := Fin.ext h
            rw [← hk', Equiv.apply_symm_apply]
        · rintro (h | h)
          · subst h
            simp
          · omega
      have hgp : GreedyPayoff σ f (σ ⟨j, hj⟩) =
          f (InitialCoalition σ (j + 1)) - f (InitialCoalition σ j) := by
        simp [GreedyPayoff]
      calc ∑ i ∈ InitialCoalition σ (j + 1), GreedyPayoff σ f i
          = ∑ i ∈ insert (σ ⟨j, hj⟩) (InitialCoalition σ j), GreedyPayoff σ f i := by
            rw [hins]
        _ = GreedyPayoff σ f (σ ⟨j, hj⟩) + ∑ i ∈ InitialCoalition σ j, GreedyPayoff σ f i :=
            Finset.sum_insert hmem
        _ = f (InitialCoalition σ (j + 1)) := by
            rw [ih, hgp]
            ring
    · have heq : InitialCoalition σ (j + 1) = InitialCoalition σ j := by
        ext k
        simp only [InitialCoalition, Finset.mem_filter, Finset.mem_univ, true_and]
        have := (σ.symm k).isLt
        omega
      rw [heq, ih]
