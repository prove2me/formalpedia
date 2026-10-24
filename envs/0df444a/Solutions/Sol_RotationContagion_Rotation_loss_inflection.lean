-- Prove2me | solution 1 for RotationContagion.Rotation.loss_inflection
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:42:01.089991+00:00
-- url     : https://prove2.me/submissions/a9c02510-8be6-443b-ba2e-e3b72f04baac

import Definitions.Def_RotationContagion_Rotation_Model
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open RotationContagion.Rotation

namespace D24Logistic

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

lemma second_deriv (P : Params) (t : ℝ) : HasDerivAt (first P) (second P t) t := by
  have he := ex_deriv P t
  have hp : 0 < 1 + ex P t := by unfold ex; positivity
  convert! (he.const_mul P.γ).div
    (((hasDerivAt_const t (1 : ℝ)).add he).pow 2) (pow_ne_zero 2 (ne_of_gt hp)) using 1 <;> try rfl
  dsimp only [second, Pi.add_apply, Pi.pow_apply]
  field_simp [ne_of_gt hp]
  ring

end D24Logistic

theorem solution (P : Params) (hP : P.Standing) :
    loss P (b P) = 1 / 2 ∧ ConvexOn ℝ (Set.Iic (b P)) (loss P) ∧
      ConcaveOn ℝ (Set.Ici (b P)) (loss P) := by
  have hγ : 0 < P.γ := hP.1
  have hc : Continuous (loss P) := continuous_iff_continuousAt.mpr
    (fun t => (D24Logistic.first_deriv P t).continuousAt)
  refine ⟨by norm_num [loss], ?_, ?_⟩
  · apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Iic (b P)) hc.continuousOn
      (fun t _ => (D24Logistic.first_deriv P t).hasDerivWithinAt)
      (fun t _ => (D24Logistic.second_deriv P t).hasDerivWithinAt)
    intro t ht
    have htb : t ≤ b P := Set.mem_Iic.mp (interior_subset ht)
    have he1 : D24Logistic.ex P t ≤ 1 := by
      unfold D24Logistic.ex
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hγ.le (sub_nonpos.mpr htb))
    unfold D24Logistic.second
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (sub_nonneg.mpr he1)
    · unfold D24Logistic.ex
      positivity
  · apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ici (b P)) hc.continuousOn
      (fun t _ => (D24Logistic.first_deriv P t).hasDerivWithinAt)
      (fun t _ => (D24Logistic.second_deriv P t).hasDerivWithinAt)
    intro t ht
    have hbt : b P ≤ t := Set.mem_Ici.mp (interior_subset ht)
    have he1 : 1 ≤ D24Logistic.ex P t := by
      unfold D24Logistic.ex
      exact Real.one_le_exp_iff.mpr (mul_nonneg hγ.le (sub_nonneg.mpr hbt))
    unfold D24Logistic.second
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (sub_nonpos.mpr he1)
    · unfold D24Logistic.ex
      positivity

#print axioms solution
