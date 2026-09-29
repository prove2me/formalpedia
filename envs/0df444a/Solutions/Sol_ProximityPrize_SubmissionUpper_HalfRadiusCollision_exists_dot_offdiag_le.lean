-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.HalfRadiusCollision.exists_dot_offdiag_le
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T05:07:46.982175+00:00
-- url     : https://prove2.me/submissions/a60a59f1-952f-461e-90a7-d369f979084f

import Mathlib
import Init
import Definitions.Def_ProximityPrize_SubmissionUpper_HalfRadiusCollision_dot
import Theorems.Thm_ProximityPrize_SubmissionUpper_HalfRadiusCollision_dot_zero_fiber_card_mul
namespace ProximityPrize.SubmissionUpper.HalfRadiusCollision

open scoped BigOperators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]










lemma _root_.solution {k : ℕ} (A : Finset (Fin k → F)) :
    ∃ v : Fin k → F,
      Fintype.card F *
          ((A.product A).filter fun xy =>
            xy.1 ≠ xy.2 ∧ dot xy.1 v = dot xy.2 v).card ≤
        A.card * (A.card - 1) := by
  classical
  let P := A.offDiag
  let off : (Fin k → F) → ℕ := fun v =>
    ∑ xy ∈ P, if dot xy.1 v = dot xy.2 v then 1 else 0
  have hPcard : P.card = A.card * (A.card - 1) := by
    simp only [P, Finset.offDiag_card, Nat.mul_sub_left_distrib, mul_one]
  have hinner (xy : (Fin k → F) × (Fin k → F)) (hxy : xy ∈ P) :
      Fintype.card F *
          (∑ v : Fin k → F, if dot xy.1 v = dot xy.2 v then 1 else 0) =
        Fintype.card (Fin k → F) := by
    have hne : xy.1 ≠ xy.2 := by
      exact (Finset.mem_offDiag.mp (by simpa only [P] using hxy)).2.2
    have hd : xy.1 - xy.2 ≠ 0 := sub_ne_zero.mpr hne
    have hfilter :
        (Finset.univ.filter fun v : Fin k → F => dot xy.1 v = dot xy.2 v).card =
          (Finset.univ.filter fun v : Fin k → F => dot (xy.1 - xy.2) v = 0).card := by
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, sub_eq_zero]
    rw [← Finset.card_filter, hfilter, Nat.mul_comm]
    exact dot_zero_fiber_card_mul hd
  have htotal :
      (∑ v : Fin k → F, Fintype.card F * off v) =
        ∑ _v : Fin k → F, P.card := by
    calc
      (∑ v : Fin k → F, Fintype.card F * off v) =
          ∑ v : Fin k → F, ∑ xy ∈ P,
            Fintype.card F * if dot xy.1 v = dot xy.2 v then 1 else 0 := by
              simp only [off, Finset.mul_sum]
      _ = ∑ xy ∈ P, ∑ v : Fin k → F,
          Fintype.card F * if dot xy.1 v = dot xy.2 v then 1 else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ xy ∈ P, Fintype.card F *
            (∑ v : Fin k → F, if dot xy.1 v = dot xy.2 v then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro xy _
              rw [Finset.mul_sum]
      _ = ∑ _xy ∈ P, Fintype.card (Fin k → F) := by
            apply Finset.sum_congr rfl
            intro xy hxy
            exact hinner xy hxy
      _ = ∑ _v : Fin k → F, P.card := by simp [Nat.mul_comm]
  obtain ⟨v, -, hv⟩ := Finset.exists_le_of_sum_le
    (s := (Finset.univ : Finset (Fin k → F))) Finset.univ_nonempty
    (show (∑ v : Fin k → F, Fintype.card F * off v) ≤
      ∑ _v : Fin k → F, P.card by rw [htotal])
  refine ⟨v, ?_⟩
  rw [← hPcard]
  have hoff :
      ((A.product A).filter fun xy =>
        xy.1 ≠ xy.2 ∧ dot xy.1 v = dot xy.2 v).card = off v := by
    rw [Finset.card_filter]
    simp only [off, P]
    rw [show A.offDiag = (A ×ˢ A).filter (fun xy => xy.1 ≠ xy.2) by
      ext xy
      rcases xy with ⟨x, y⟩
      simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨hx, hy, hne⟩
        exact ⟨⟨hx, hy⟩, hne⟩
      · rintro ⟨⟨hx, hy⟩, hne⟩
        exact ⟨hx, hy, hne⟩]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro xy _
    by_cases hne : xy.1 ≠ xy.2 <;>
      by_cases heq : dot xy.1 v = dot xy.2 v <;> simp [hne, heq]
  simpa only [hoff] using hv
end HalfRadiusCollision
end SubmissionUpper
end ProximityPrize
