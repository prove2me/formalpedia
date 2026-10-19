-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P09.leakageErrorComponent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:00:20.097981+00:00
-- url     : https://prove2.me/submissions/56c05f86-b05b-4652-88dd-30675a94d2d6

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false

noncomputable section
open scoped Matrix ComplexOrder NNReal ENNReal
open QAlgorithms QAlgorithms.ErrorMitigation QAlgorithms.Papers.Independent.Independent1.P09
open Filter Topology

private lemma factor_rational (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    leakageFactor p = Real.sqrt (1-p) / (1 + Real.sqrt (1-p)) := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr hp1)
  have hd : 1 + Real.sqrt (1-p) ≠ 0 := by positivity
  unfold leakageFactor
  apply (div_eq_div_iff (ne_of_gt hp) hd).2
  nlinarith

private lemma factor_difference (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    leakageFactor p - 1/2 = -p / (2 * (1 + Real.sqrt (1-p))^2) := by
  rw [factor_rational p hp hp1]
  have hs := Real.sq_sqrt (sub_nonneg.mpr hp1)
  have hd : 1 + Real.sqrt (1-p) ≠ 0 := by positivity
  field_simp
  nlinarith

theorem solution :
    (∀ p : ℝ, 0 < p → p ≤ 1 → ∀ X : Matrix Bool Bool ℂ,
      leakageMap p X = (1-p : ℂ) • X + (p : ℂ) • leakageComponent p X) ∧
    Filter.Tendsto leakageFactor (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1/2 : ℝ)) ∧
    Asymptotics.IsBigO (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (fun p => leakageFactor p-1/2) (fun p : ℝ => p) := by
  classical
  have hev : ∀ᶠ p : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < p ∧ p ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with p hp hp1
    exact ⟨hp, le_of_lt hp1⟩
  refine ⟨?_, ?_, ?_⟩
  · intro p hp hp1 X
    have hs : (Real.sqrt (1-p) : ℂ)^2 = 1-p := by
      exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hp1)
    have hf : (p : ℂ) * (leakageFactor p : ℂ) =
        (Real.sqrt (1-p) : ℂ) - (1-p) := by
      exact_mod_cast (show p * leakageFactor p = Real.sqrt (1-p) - (1-p) by
        unfold leakageFactor
        field_simp)
    change krausApply (fun _ : Fin 1 => Matrix.diagonal fun b : Bool =>
      if b then (Real.sqrt (1-p) : ℂ) else 1) X = _
    ext i j
    cases i <;> cases j <;>
      simp [krausApply, leakageComponent,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single_apply,
        Fintype.sum_bool, Complex.star_def, mul_add, add_mul] <;>
      first | ring1 | linear_combination -(X false true) * hf
            | linear_combination -(X true false) * hf
            | linear_combination (X true true) * hs
  · have hcont : ContinuousAt (fun p : ℝ =>
        Real.sqrt (1-p) / (1 + Real.sqrt (1-p))) 0 := by
      fun_prop (disch := norm_num)
    have ht : Tendsto (fun p : ℝ => Real.sqrt (1-p) / (1 + Real.sqrt (1-p)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (1/2 : ℝ)) := by
      convert hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ))) using 1 <;> norm_num
    apply ht.congr'
    filter_upwards [hev] with p hp
    exact (factor_rational p hp.1 hp.2).symm
  · apply Asymptotics.IsBigO.of_bound (1/2 : ℝ)
    filter_upwards [hev] with p hp
    rw [factor_difference p hp.1 hp.2]
    simp only [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hp.1]
    have hd : 1 ≤ (1 + Real.sqrt (1-p))^2 := by
      nlinarith [Real.sqrt_nonneg (1-p)]
    rw [abs_of_pos (show 0 < 2 * (1 + Real.sqrt (1-p))^2 by positivity)]
    apply (div_le_iff₀ (show 0 < 2 * (1 + Real.sqrt (1-p))^2 by positivity)).2
    nlinarith

#print axioms solution
