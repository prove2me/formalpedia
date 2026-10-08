-- Prove2me | solution 1 for SchedComplexity.NoWait.formula_9_delay
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:42:57.39928+00:00
-- url     : https://prove2.me/submissions/a458a415-907c-4b39-a65d-9f8c8acb94ee

import Mathlib
import Definitions.Def_SchedComplexity_NoWait_NoWaitFlowShop



namespace SchedComplexity.NoWait

theorem f9_core {n m : ℕ} (p : Fin n → Fin m → ℕ) (hm : 0 < m) (j k : Fin n)
    (hjk : j ≠ k) :
    IsLeast {δ : ℤ | 0 ≤ δ ∧ ∀ r : Fin m, (cum p j (r.val + 1) : ℤ) ≤ δ + (cum p k r.val : ℤ)}
      (delay p hm j k) := by
  constructor
  · refine ⟨?_, ?_⟩
    · have h := Finset.le_sup' (fun r : Fin m => (cum p j (r.val + 1) : ℤ) - (cum p k r.val : ℤ))
        (Finset.mem_univ (⟨0, hm⟩ : Fin m))
      have h2 : (0:ℤ) ≤ (cum p j (0 + 1) : ℤ) - (cum p k 0 : ℤ) := by
        simp [cum]
        exact Finset.sum_nonneg (fun _ _ => by positivity)
      exact le_trans h2 h
    · intro r
      have h := Finset.le_sup' (fun r : Fin m => (cum p j (r.val + 1) : ℤ) - (cum p k r.val : ℤ))
        (Finset.mem_univ r)
      unfold delay
      linarith
  · rintro δ ⟨_, hδ⟩
    unfold delay
    apply Finset.sup'_le
    intro r _
    have := hδ r
    linarith

end SchedComplexity.NoWait

open SchedComplexity.NoWait


theorem solution {n m : ℕ} (p : Fin n → Fin m → ℕ) (hm : 0 < m) (j k : Fin n)
    (hjk : j ≠ k) :
    IsLeast {δ : ℤ | 0 ≤ δ ∧ ∀ r : Fin m, (cum p j (r.val + 1) : ℤ) ≤ δ + (cum p k r.val : ℤ)}
      (delay p hm j k) := by
  exact f9_core p hm j k hjk
