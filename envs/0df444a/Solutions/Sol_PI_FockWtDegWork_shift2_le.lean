-- Prove2me | solution 1 for PI.FockWtDegWork.shift2_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:40:20.607568+00:00
-- url     : https://prove2.me/submissions/a919a384-bdc4-465e-9632-59bc36e3d7b7

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight
import Theorems.Thm_PI_FockWtDegWork_abs_le_of
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open FockH1Action
namespace PI.FockWtDegWork
private theorem sum_add_half_add_sum_neg_sub_half (A B : ℕ) (f : Fin A → ℚ) (g : Fin B → ℚ) :
    ∑ c, (f c + 1 / 2) + ∑ c, (-g c - 1 / 2) = (∑ c, f c) - (∑ c, g c) + ((A : ℚ) - B) / 2 := by
  first
    | (simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring)
    | (simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]; ring)
private theorem sum_neg_sub_half_add_sum_add_half (A B : ℕ) (f : Fin A → ℚ) (g : Fin B → ℚ) :
    ∑ c, (-f c - 1 / 2) + ∑ c, (g c + 1 / 2) = (∑ c, g c) - (∑ c, f c) - ((A : ℚ) - B) / 2 := by
  first
    | (simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring)
    | (simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]; ring)
end PI.FockWtDegWork
end
end

set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockWtDegWork
namespace PI.FockWtDegWork
theorem _root_.solution {p q r s : ℕ} (α : Ln p q r s →₀ ℕ) (c : Ix r s) :
    |shiftNu (cPair p q) (fun b => W2 b α) c| ≤ ∑ a : Ix p q, (α (a, c) : ℚ) := by
  rw [Fintype.sum_sum_type]
  cases c with
  | inl k =>
    have hL : W2 (Sum.inl k) α = ∑ a : Fin p, ((α (Sum.inl a, Sum.inl k) : ℚ) + 1 / 2) +
        ∑ a : Fin q, (-(α (Sum.inr a, Sum.inl k) : ℚ) - 1 / 2) := by
      rw [W2, Fintype.sum_sum_type] <;> first | rfl | simp [lw, FockH1Action.linePos]
    have hx : FockH1Action.shiftNu (FockH1Action.cPair p q) (fun b => W2 b α) (Sum.inl k) =
        (∑ a : Fin p, (α (Sum.inl a, Sum.inl k) : ℚ)) - ∑ a : Fin q, (α (Sum.inr a, Sum.inl k) : ℚ) := by
      show W2 (Sum.inl k) α - FockH1Action.cPair p q = _
      rw [hL, sum_add_half_add_sum_neg_sub_half, FockH1Action.cPair]
      ring
    exact abs_le_of _ _ _ (by exact Finset.sum_nonneg fun a _ => Nat.cast_nonneg _)
      (by exact Finset.sum_nonneg fun a _ => Nat.cast_nonneg _) hx
  | inr k =>
    have hL : W2 (Sum.inr k) α = ∑ a : Fin p, (-(α (Sum.inl a, Sum.inr k) : ℚ) - 1 / 2) +
        ∑ a : Fin q, ((α (Sum.inr a, Sum.inr k) : ℚ) + 1 / 2) := by
      rw [W2, Fintype.sum_sum_type] <;> first | rfl | simp [lw, FockH1Action.linePos]
    have hx : FockH1Action.shiftNu (FockH1Action.cPair p q) (fun b => W2 b α) (Sum.inr k) =
        (∑ a : Fin q, (α (Sum.inr a, Sum.inr k) : ℚ)) - ∑ a : Fin p, (α (Sum.inl a, Sum.inr k) : ℚ) := by
      show W2 (Sum.inr k) α + FockH1Action.cPair p q = _
      rw [hL, sum_neg_sub_half_add_sum_add_half, FockH1Action.cPair]
      ring
    exact (abs_le_of _ _ _ (by exact Finset.sum_nonneg fun a _ => Nat.cast_nonneg _)
      (by exact Finset.sum_nonneg fun a _ => Nat.cast_nonneg _) hx).trans_eq (add_comm _ _)
end PI.FockWtDegWork
