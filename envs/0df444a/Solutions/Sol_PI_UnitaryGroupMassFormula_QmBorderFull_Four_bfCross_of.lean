-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.Four.bfCross_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:06:32.508547+00:00
-- url     : https://prove2.me/submissions/8ed0fd20-5a99-4003-becc-8c8caeb7b861

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipTwoSuccAboveComp
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_Tm_of_ne
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_inner
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_skip_two_succAbove_comp_alt
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_sign_pair_succAbove_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_sign_two_succAbove_left
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_triple
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_mid_comp
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_mid_val
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_scal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Formalism.REAL
noncomputable section
namespace PI.UnitaryGroupMassFormula.QmBorderFull.Four
open PI
private theorem intCast_mul_mul_mul_eq_of_mul_eq {A : Type} [Ring A] (c₁ c₂ c₀ a : ℤ) (X S : A) (h : c₁ * c₂ = c₀ * a) :
    (c₁ : A) * (((c₂ : A) * X) * S) = (c₀ : A) * ((a : A) * (X * S)) := by
  rw [mul_assoc (c₂ : A), ← mul_assoc, ← mul_assoc (c₀ : A), ← Int.cast_mul, ← Int.cast_mul, h]
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
end
end

set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull PI.UnitaryGroupMassFormula.QmBorderFull.Four
open PI
namespace PI.UnitaryGroupMassFormula.QmBorderFull.Four
theorem _root_.solution (hRow : PI.QmRowExp) (_hSkip : PI.QmSkip) : BFCross := by
  intro A _ _ n k E e es v hG hB u w
  obtain ⟨hF, hR⟩ := hRow
  obtain ⟨_, _, hve, hves⟩ := hB
  cases k with
  | zero =>
    rw [Fin.sum_univ_zero]
    symm
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun w' _ => Finset.sum_eq_zero fun x _ =>
      Finset.sum_eq_zero fun x' _ => if_neg fun h => h.1 (Fin.ext ?_))
    have := w.isLt
    have := w'.isLt
    omega
  | succ k =>
    have ht := triple w (M := A) (fun w' x x' => ((sg2 w w' * sg2 x x' : ℤ) : A) *
      (E es (v x) * qminor E (v ∘ skip2 (min w w') (max w w')) (v ∘ skip2 (min x x') (max x x')) (u - 2) *
        E e (v x') * E (v w') es))
    beta_reduce at ht
    rw [ht, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mid_comp, mid_comp, mid_val, Tm_of_ne E _ (a := (v ∘ w.succAbove) j) (hves (w.succAbove j)),
      inner hR hF E hG e es _ v hve hves (u - 1), Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hq1 : v ∘ skip2 (min w (w.succAbove j)) (max w (w.succAbove j)) = (v ∘ w.succAbove) ∘ j.succAbove := by
      funext i
      simp only [Function.comp_apply, skip_two_succAbove_comp_alt]
    have hq2 : v ∘ skip2 (min (x.succAbove y) x) (max (x.succAbove y) x) =
        (v ∘ x.succAbove) ∘ y.succAbove := by
      rw [min_comm, max_comm]
      funext i
      simp only [Function.comp_apply, skip_two_succAbove_comp_alt]
    have hu : u - 1 - 1 = u - 2 := by ring
    have hj : (j.castSucc.succ : ℕ) = (j : ℕ) + 1 := by simp
    rw [hq1, hq2, ← hu, sign_pair_succAbove_right, sign_two_succAbove_left, hj]
    exact intCast_mul_mul_mul_eq_of_mul_eq _ _ _ _ _ _ (scal k w j x y)
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
