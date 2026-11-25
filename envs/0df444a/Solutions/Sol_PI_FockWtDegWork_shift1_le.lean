-- Prove2me | solution 1 for PI.FockWtDegWork.shift1_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:40:31.596682+00:00
-- url     : https://prove2.me/submissions/2724e476-6de2-47fb-ac0a-948dfd6527b0

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
theorem _root_.solution {p q r s : ℕ} (α : Ln p q r s →₀ ℕ) (a : Ix p q) :
    |shiftNu (cPair r s) (fun b => W1 b α) a| ≤ ∑ c : Ix r s, (α (a, c) : ℚ) := by
  rw [Fintype.sum_sum_type]
  cases a with
  | inl i =>
    have hL : W1 (Sum.inl i) α = ∑ c : Fin r, ((α (Sum.inl i, Sum.inl c) : ℚ) + 1 / 2) +
        ∑ c : Fin s, (-(α (Sum.inl i, Sum.inr c) : ℚ) - 1 / 2) := by
      rw [W1, Fintype.sum_sum_type] <;> first | rfl | simp [lw, FockH1Action.linePos]
    have hx : FockH1Action.shiftNu (FockH1Action.cPair r s) (fun b => W1 b α) (Sum.inl i) =
        (∑ c : Fin r, (α (Sum.inl i, Sum.inl c) : ℚ)) - ∑ c : Fin s, (α (Sum.inl i, Sum.inr c) : ℚ) := by
      show W1 (Sum.inl i) α - FockH1Action.cPair r s = _
      rw [hL, sum_add_half_add_sum_neg_sub_half, FockH1Action.cPair]
      ring
    exact abs_le_of _ _ _ (by exact Finset.sum_nonneg fun c _ => Nat.cast_nonneg _)
      (by exact Finset.sum_nonneg fun c _ => Nat.cast_nonneg _) hx
  | inr j =>
    have hL : W1 (Sum.inr j) α = ∑ c : Fin r, (-(α (Sum.inr j, Sum.inl c) : ℚ) - 1 / 2) +
        ∑ c : Fin s, ((α (Sum.inr j, Sum.inr c) : ℚ) + 1 / 2) := by
      rw [W1, Fintype.sum_sum_type] <;> first | rfl | simp [lw, FockH1Action.linePos]
    have hx : FockH1Action.shiftNu (FockH1Action.cPair r s) (fun b => W1 b α) (Sum.inr j) =
        (∑ c : Fin s, (α (Sum.inr j, Sum.inr c) : ℚ)) - ∑ c : Fin r, (α (Sum.inr j, Sum.inl c) : ℚ) := by
      show W1 (Sum.inr j) α + FockH1Action.cPair r s = _
      rw [hL, sum_neg_sub_half_add_sum_add_half, FockH1Action.cPair]
      ring
    exact (abs_le_of _ _ _ (by exact Finset.sum_nonneg fun c _ => Nat.cast_nonneg _)
      (by exact Finset.sum_nonneg fun c _ => Nat.cast_nonneg _) hx).trans_eq (add_comm _ _)
end PI.FockWtDegWork
