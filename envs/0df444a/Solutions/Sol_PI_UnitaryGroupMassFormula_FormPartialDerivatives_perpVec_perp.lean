-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FormPartialDerivatives.perpVec_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:11.288695+00:00
-- url     : https://prove2.me/submissions/cabc6fae-ed86-47b4-8fdb-486e4f410ded

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_PerpVecPerpSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_PerpendicularDeterminants_PerpVecOfPerp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FormPartialDerivatives
open ReciprocityTheory.ChartRestriction.G.TB
namespace PI.UnitaryGroupMassFormula.FormPartialDerivatives
theorem _root_.solution (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) (c : Fin p) :
    h (perpVec h e e' g) (e c) = 0 := by
  have hentry : ∀ a', hMat h e e' a' c = h (e' a') (e c) := fun _ => rfl
  have key : ∀ a, ∑ a', (hMat h e e').adjugate a a' * h (e' a') (e c) =
      if a = c then (hMat h e e').det else 0 := by
    intro a
    have hk := congrFun (congrFun (Matrix.adjugate_mul (hMat h e e')) a) c
    rw [Matrix.mul_apply] at hk
    simp only [hentry] at hk
    rw [hk, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  simp only [perpVec, map_sub, map_smul, map_sum, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul]
  have hsum : ∑ a, ∑ a', (hMat h e e').adjugate a a' * h g (e a) * h (e' a') (e c) =
      (hMat h e e').det * h g (e c) := by
    calc ∑ a, ∑ a', (hMat h e e').adjugate a a' * h g (e a) * h (e' a') (e c)
        = ∑ a, h g (e a) * ∑ a', (hMat h e e').adjugate a a' * h (e' a') (e c) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a' _ => ?_
          ring
      _ = (hMat h e e').det * h g (e c) := by
          simp only [key, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
  rw [hsum]
  ring
end PI.UnitaryGroupMassFormula.FormPartialDerivatives
