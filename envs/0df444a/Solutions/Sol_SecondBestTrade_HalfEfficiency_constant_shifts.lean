-- Prove2me | solution 1 for SecondBestTrade.HalfEfficiency.constant_shifts
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-13T15:27:48.54356+00:00
-- url     : https://prove2.me/submissions/b6d7f34f-5d2a-443a-b340-7d69bc3e51d0

import Definitions.Def_SecondBestTrade_HalfEfficiency_PaymentTransforms

open scoped BigOperators
open SecondBestTrade.HalfEfficiency

noncomputable section

private theorem totalPrior (N : Market) : ∑ v, prior N v = 1 := by
  classical
  simpa [prior, N.mass_sum] using (Fintype.prod_sum N.mass).symm

theorem solution (N : Market) (m : SignedMechanism N)
    (_hx : feasible N m.q) (hbic : BIC N m) (hir : IR N m) (d : Agent N → ℝ) :
    (∀ a t r, U N (shifted N m d) a t r = U N m a t r - d a) ∧
    BIC N (shifted N m d) ∧
    (IR N (shifted N m d) ↔ ∀ a, d a ≤ minUtility N m a) := by
  classical
  have shift (a : Agent N) (t r : Ty N a) :
      U N (shifted N m d) a t r = U N m a t r - d a := by
    unfold U expect
    simp only [shifted, ← sub_sub, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      totalPrior, one_mul]
  refine ⟨shift, fun a t r => ?_, ?_⟩
  · simpa only [shift] using sub_le_sub_right (hbic a t r) (d a)
  · constructor
    · intro h a
      apply le_csInf
      · exact ⟨_, ⟨⟨0, N.nt_pos a⟩, rfl⟩⟩
      · rintro _ ⟨t, rfl⟩
        exact sub_nonneg.mp ((shift a t t) ▸ h a t)
    · intro h a t
      rw [shift]
      apply sub_nonneg.mpr
      exact (h a).trans (csInf_le ⟨0, by rintro _ ⟨s, rfl⟩; exact hir a s⟩ ⟨t, rfl⟩)
