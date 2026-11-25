-- Prove2me | solution 1 for PI.FockOneDegW.Core.shift_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:47:33.730647+00:00
-- url     : https://prove2.me/submissions/251982a9-6a40-4261-8163-6a2f0d9ae278

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Theorems.Thm_PI_FockOneDegW_Core_abs_sub_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.Core
open PI.FockOneDegW PI.FockOneDegW.Inner PI.FockOneDegW.Diag
variable {p q r s : ℕ}
namespace PI.FockOneDegW.Core
theorem _root_.solution (α : Ln p q r s →₀ ℕ)
    (hrow : ∀ (a : Ix p q) (c d : Ix r s), linePos ((a, c) : Ln p q r s) = false →
      linePos ((a, d) : Ln p q r s) = true → α (a, c) = 0 ∨ α (a, d) = 0) (a : Ix p q) :
    |shiftNu (cPair r s) (fun b => W1 b α) a| = ∑ c : Ix r s, (α (a, c) : ℚ) := by
  rcases a with i | i
  · rw [Fintype.sum_sum_type]
    have hx : shiftNu (cPair r s) (fun b => W1 b α) (Sum.inl i) =
        (∑ c : Fin r, (α (Sum.inl i, Sum.inl c) : ℚ)) -
          ∑ c : Fin s, (α (Sum.inl i, Sum.inr c) : ℚ) := by
      simp [shiftNu, W1, cPair, Fintype.sum_sum_type, lw, linePos, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      ring
    rw [hx]
    apply abs_sub_of _ _ (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
      (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
    by_cases hA : ∀ c : Fin r, α (Sum.inl i, Sum.inl c) = 0
    · left; exact Finset.sum_eq_zero fun c _ => by simp [hA c]
    · right
      push_neg at hA
      obtain ⟨c0, hc0⟩ := hA
      refine Finset.sum_eq_zero fun d _ => ?_
      have := (hrow (Sum.inl i) (Sum.inr d) (Sum.inl c0) rfl rfl).resolve_right hc0
      simp [this]
  · rw [Fintype.sum_sum_type, add_comm]
    have hx : shiftNu (cPair r s) (fun b => W1 b α) (Sum.inr i) =
        (∑ c : Fin s, (α (Sum.inr i, Sum.inr c) : ℚ)) -
          ∑ c : Fin r, (α (Sum.inr i, Sum.inl c) : ℚ) := by
      simp [shiftNu, W1, cPair, Fintype.sum_sum_type, lw, linePos, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      ring
    rw [hx]
    apply abs_sub_of _ _ (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
      (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
    by_cases hA : ∀ c : Fin s, α (Sum.inr i, Sum.inr c) = 0
    · left; exact Finset.sum_eq_zero fun c _ => by simp [hA c]
    · right
      push_neg at hA
      obtain ⟨c0, hc0⟩ := hA
      refine Finset.sum_eq_zero fun d _ => ?_
      have := (hrow (Sum.inr i) (Sum.inl d) (Sum.inr c0) rfl rfl).resolve_right hc0
      simp [this]
end PI.FockOneDegW.Core
