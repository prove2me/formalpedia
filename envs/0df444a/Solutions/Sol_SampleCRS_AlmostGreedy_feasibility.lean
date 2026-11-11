-- Prove2me | solution 1 for SampleCRS.AlmostGreedy.feasibility
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T00:15:11.883966+00:00
-- url     : https://prove2.me/submissions/e9aeff9d-5b6e-4a97-a91c-fb258f235d1c

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_run
open SampleCRS.AlmostGreedy


/-- The pathwise feasibility clause of Theorem 4.1, p.14. -/
theorem solution (n k : ℕ) (hk : 1 ≤ k) :
    ∀ (σ : Equiv.Perm (Fin n)) (X Y : Fin n → Bool) (Q : Bool),
      (run k σ X Y Q).card ≤ k := by
  intro σ X Y Q
  have hstep : ∀ (s : Finset (Fin n) × Bool) (i : Fin n),
      s.1.card ≤ k → (step k X Y Q s i).1.card ≤ k := by
    intro s i hs
    unfold step
    split_ifs <;>
      first | exact hs | exact (Finset.card_insert_le i s.1).trans (by omega)
  have hfold : ∀ (l : List (Fin n)) (s : Finset (Fin n) × Bool),
      s.1.card ≤ k → (l.foldl (fun s t => step k X Y Q s (σ t)) s).1.card ≤ k := by
    intro l
    induction l with
    | nil => intro s hs; exact hs
    | cons a l ih =>
      intro s hs
      exact ih _ (hstep s (σ a) hs)
  exact hfold _ _ (by simp)






