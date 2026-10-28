-- Prove2me | solution 1 for RotationContagion.Rotation.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:40:02.843231+00:00
-- url     : https://prove2.me/submissions/c14d26c7-68e9-4535-854b-f9510a4105f8

import Definitions.Def_RotationContagion_Rotation_Model
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open RotationContagion.Rotation

namespace D26Rotation

noncomputable def ex (P : Params) (t : ℝ) := Real.exp (P.γ * (t - b P))
noncomputable def first (P : Params) (t : ℝ) := P.γ * ex P t / (1 + ex P t) ^ 2
noncomputable def second (P : Params) (t : ℝ) :=
  P.γ ^ 2 * ex P t * (1 - ex P t) / (1 + ex P t) ^ 3

lemma ex_deriv (P : Params) (t : ℝ) : HasDerivAt (ex P) (P.γ * ex P t) t := by
  have harg : HasDerivAt (fun s : ℝ => P.γ * (s - b P)) P.γ t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).sub_const (b P)).const_mul P.γ
  convert! harg.exp using 1 <;> try rfl
  unfold ex
  ring

lemma first_deriv (P : Params) (t : ℝ) : HasDerivAt (loss P) (first P t) t := by
  have he := ex_deriv P t
  have hp : 0 < 1 + ex P t := by unfold ex; positivity
  convert! he.div ((hasDerivAt_const t (1 : ℝ)).add he) (ne_of_gt hp) using 1 <;> try rfl
  dsimp only [first, Pi.add_apply]
  ring


lemma obj_deriv (P : Params) (t : ℝ) :
    HasDerivAt (relaxedObj P) (first P t - first P (P.R - t)) t := by
  have hleft := first_deriv P t
  have hright := (first_deriv P (P.R - t)).comp t
    ((hasDerivAt_const t P.R).sub (hasDerivAt_id t))
  convert hleft.add hright using 1 <;>
    (first | rfl | ((try simp only [relaxedObj, Function.comp_def, id_eq]); ring))

lemma rate_formula (P : Params) (t : ℝ) :
    first P t - first P (P.R - t) =
      P.γ * (ex P t - ex P (P.R - t)) * (1 - ex P t * ex P (P.R - t)) /
        ((1 + ex P t) ^ 2 * (1 + ex P (P.R - t)) ^ 2) := by
  have h1 : 1 + ex P t ≠ 0 := by unfold ex; positivity
  have h2 : 1 + ex P (P.R - t) ≠ 0 := by unfold ex; positivity
  dsimp [first]
  field_simp [h1, h2] <;> ring

lemma product_lt (P : Params) (hγ : 0 < P.γ) (hm : P.R / 2 < b P) (t : ℝ) :
    ex P t * ex P (P.R - t) < 1 := by
  unfold ex
  rw [← Real.exp_add]
  apply Real.exp_lt_one_iff.mpr
  have hn : P.γ * (P.R - 2 * b P) < 0 := mul_neg_of_pos_of_neg hγ (by linarith)
  nlinarith only [hn]

lemma product_gt (P : Params) (hγ : 0 < P.γ) (hm : b P < P.R / 2) (t : ℝ) :
    1 < ex P t * ex P (P.R - t) := by
  unfold ex
  rw [← Real.exp_add]
  apply Real.one_lt_exp_iff.mpr
  have hn : 0 < P.γ * (P.R - 2 * b P) := mul_pos hγ (by linarith)
  nlinarith only [hn]

lemma left_ex_lt (P : Params) (hγ : 0 < P.γ) (t : ℝ) (ht : t < P.R / 2) :
    ex P t < ex P (P.R - t) := by
  apply Real.exp_lt_exp.mpr
  exact mul_lt_mul_of_pos_left (by linarith) hγ

lemma right_ex_lt (P : Params) (hγ : 0 < P.γ) (t : ℝ) (ht : P.R / 2 < t) :
    ex P (P.R - t) < ex P t := by
  apply Real.exp_lt_exp.mpr
  exact mul_lt_mul_of_pos_left (by linarith) hγ

lemma denom_pos (P : Params) (t : ℝ) :
    0 < (1 + ex P t) ^ 2 * (1 + ex P (P.R - t)) ^ 2 := by
  unfold ex
  positivity

end D26Rotation

theorem solution (P : Params) (hP : P.Standing) :
    (P.R / 2 < b P →
      StrictAntiOn (relaxedObj P) (Set.Iic (P.R / 2)) ∧
        StrictMonoOn (relaxedObj P) (Set.Ici (P.R / 2))) ∧
    (b P < P.R / 2 →
      StrictMonoOn (relaxedObj P) (Set.Iic (P.R / 2)) ∧
        StrictAntiOn (relaxedObj P) (Set.Ici (P.R / 2))) := by
  have hc : Continuous (relaxedObj P) :=
    continuous_iff_continuousAt.mpr (fun t => (D26Rotation.obj_deriv P t).continuousAt)
  constructor
  · intro hm
    constructor
    · apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Iic (P.R / 2)) hc.continuousOn
        (fun t _ => (D26Rotation.obj_deriv P t).hasDerivWithinAt)
      intro t ht
      rw [interior_Iic] at ht
      rw [D26Rotation.rate_formula]
      exact div_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos
          (mul_neg_of_pos_of_neg hP.1 (sub_neg.mpr (D26Rotation.left_ex_lt P hP.1 t ht)))
          (sub_pos.mpr (D26Rotation.product_lt P hP.1 hm t)))
        (D26Rotation.denom_pos P t)
    · apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici (P.R / 2)) hc.continuousOn
        (fun t _ => (D26Rotation.obj_deriv P t).hasDerivWithinAt)
      intro t ht
      rw [interior_Ici] at ht
      rw [D26Rotation.rate_formula]
      exact div_pos
        (mul_pos
          (mul_pos hP.1 (sub_pos.mpr (D26Rotation.right_ex_lt P hP.1 t ht)))
          (sub_pos.mpr (D26Rotation.product_lt P hP.1 hm t)))
        (D26Rotation.denom_pos P t)
  · intro hm
    constructor
    · apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Iic (P.R / 2)) hc.continuousOn
        (fun t _ => (D26Rotation.obj_deriv P t).hasDerivWithinAt)
      intro t ht
      rw [interior_Iic] at ht
      rw [D26Rotation.rate_formula]
      exact div_pos
        (mul_pos_of_neg_of_neg
          (mul_neg_of_pos_of_neg hP.1 (sub_neg.mpr (D26Rotation.left_ex_lt P hP.1 t ht)))
          (sub_neg.mpr (D26Rotation.product_gt P hP.1 hm t)))
        (D26Rotation.denom_pos P t)
    · apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici (P.R / 2)) hc.continuousOn
        (fun t _ => (D26Rotation.obj_deriv P t).hasDerivWithinAt)
      intro t ht
      rw [interior_Ici] at ht
      rw [D26Rotation.rate_formula]
      exact div_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg
          (mul_pos hP.1 (sub_pos.mpr (D26Rotation.right_ex_lt P hP.1 t ht)))
          (sub_neg.mpr (D26Rotation.product_gt P hP.1 hm t)))
        (D26Rotation.denom_pos P t)

#print axioms solution

