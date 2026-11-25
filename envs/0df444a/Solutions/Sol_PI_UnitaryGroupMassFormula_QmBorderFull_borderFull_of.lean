-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.borderFull_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:41:46.224743+00:00
-- url     : https://prove2.me/submissions/15788b10-0037-4c5d-af77-1eb9ad010ca8

import Definitions.Def_Formalism_PeriodIntegrals_QmBorderFull
import Definitions.Def_Formalism_PeriodIntegrals_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_PeriodIntegrals_QmSkip
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_tm_comm_E
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_bL_last
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
namespace PI.UnitaryGroupMassFormula.QmBorderFull
open PI
private theorem mul_intCast_mul_eq_intCast_mul_mul {A : Type*} [Ring A] (s x : A) (z : ℤ) :
    s * ((z : A) * x) = (z : A) * (s * x) := by
  rw [← mul_assoc, ← mul_assoc, (Int.cast_commute z s).symm.eq]
end PI.UnitaryGroupMassFormula.QmBorderFull
end
end

set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull
open PI
namespace PI.UnitaryGroupMassFormula.QmBorderFull
theorem _root_.solution (hFC : ExpFirstCol) (hS : BorderS) (hM : BFMid) : BorderFull := by
  unfold PI.ExpFirstCol at hFC
  unfold PI.BorderS at hS
  unfold BFMid at hM
  unfold PI.BorderFull
  intro A _ _ n m E e es v hE hv u
  have hv2 : Function.Injective v ∧ e ≠ es ∧ (∀ j, v j ≠ e) ∧ ∀ j, v j ≠ es := hv
  obtain ⟨_, hne, hve, _⟩ := hv2
  have hmid := hM A n m E e es v hE hv u
  have hs : PI.bE e (PI.bS v es) ∘ Fin.succ = PI.bS v es := by
    funext i
    simp [PI.bE]
  have h0v : PI.bE e (PI.bS v es) 0 = e := by simp [PI.bE]
  have hLv : PI.bE e (PI.bS v es) (Fin.last m).succ = es := by simp [PI.bE, PI.bS]
  have hL : PI.bE e (PI.bS v es) ∘ ((Fin.last m).succ).succAbove = PI.bE e v := by
    rw [Fin.succ_last]
    exact bL_last e es v
  have hgen : Formalism.REAL.Tm E u es e = E es e := by
    simp [Formalism.REAL.Tm, hne.symm]
  have hu : u - 1 - (m : ℂ) = u - (m : ℂ) - 1 := by ring
  have hT2 : Formalism.REAL.Tm E u e e * ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
        (E es (v x) * Formalism.REAL.qminor E (v ∘ PI.skip1 w) (v ∘ PI.skip1 x) (u - 1) * E (v w) es)
      = ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
        (E es (v x) * Formalism.REAL.Tm E u e e * Formalism.REAL.qminor E (v ∘ PI.skip1 w) (v ∘ PI.skip1 x) (u - 1) * E (v w) es) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_intCast_mul_eq_intCast_mul_mul]
    congr 1
    rw [← mul_assoc, ← mul_assoc, tm_comm_E E hE u e es (v x) hne (hve x)]
  rw [hFC A n (m + 1) E (PI.bE e (PI.bS v es)) (PI.bE e (PI.bS v es)) u,
    Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  first
  | simp only [hmid]
  | rw [Finset.sum_congr rfl (fun w _ => hmid w)]
  rw [Fin.succAbove_zero, hs, h0v, hL, hLv, hgen]
  simp only [Fin.val_zero, pow_zero, Int.cast_one, one_mul, Fin.val_succ, Fin.val_last]
  rw [hS A n m E e es v hE hv (u - 1), hu, mul_sub (Formalism.REAL.Tm E u e e), hT2,
    ← mul_assoc (Formalism.REAL.Tm E u e e) (Formalism.REAL.qminor E v v (u - 1))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  abel
end PI.UnitaryGroupMassFormula.QmBorderFull
