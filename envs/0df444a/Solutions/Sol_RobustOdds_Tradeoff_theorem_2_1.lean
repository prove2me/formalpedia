-- Prove2me | solution 1 for RobustOdds.Tradeoff.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:15:44.345986+00:00
-- url     : https://prove2.me/submissions/2be02888-a037-4e51-951a-69a374f34425

import Mathlib
import Definitions.Def_RobustOdds_Tradeoff_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open RobustOdds.Tradeoff

namespace RRAux_RT

lemma meas_vecCons {d : ℕ} : Measurable (fun q : ℝ × (Fin d → ℝ) => (Matrix.vecCons q.1 q.2 : Fin (d+1) → ℝ)) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using measurable_fst
  · simp only [Matrix.cons_val_succ]; exact (measurable_pi_apply j).comp measurable_snd

lemma meas_vecCons' {d : ℕ} (a : ℝ) : Measurable (fun z : (Fin d → ℝ) => (Matrix.vecCons a z : Fin (d+1) → ℝ)) :=
  meas_vecCons.comp (measurable_const.prodMk measurable_id)

instance (d : ℕ) (η y : ℝ) : IsProbabilityMeasure (weakLaw d η y) := by
  unfold weakLaw; infer_instance

lemma condLaw_apply (d : ℕ) (p η y : ℝ) {S : Set (Fin (d+1) → ℝ)} (hS : MeasurableSet S) :
    condLaw d p η y S = ENNReal.ofReal p * weakLaw d η y {z | Matrix.vecCons y z ∈ S}
      + ENNReal.ofReal (1 - p) * weakLaw d η y {z | Matrix.vecCons (-y) z ∈ S} := by
  unfold condLaw
  rw [Measure.map_apply meas_vecCons hS, Measure.prod_apply (meas_vecCons hS)]
  unfold x1Law
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac,
    lintegral_dirac]
  rfl

lemma shift_map (d : ℕ) (η y c : ℝ) (hc : c = - 2 * η * y) :
    (weakLaw d η y).map (fun z i => z i + c) = weakLaw d η (-y) := by
  unfold weakLaw
  rw [Measure.pi_map_pi (fun _ => (measurable_add_const c).aemeasurable)]
  congr 1; funext i
  rw [gaussianReal_map_add_const]; congr 1; rw [hc]; ring


lemma shiftAdv_vecCons (d : ℕ) (η y a : ℝ) (z : Fin d → ℝ) :
    shiftAdv d η y (Matrix.vecCons a z) = Matrix.vecCons a (fun i => z i + (-2 * η * y)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [shiftAdv]
  · simp [shiftAdv]; ring

lemma shift_set (d : ℕ) (η y a t : ℝ) (f : (Fin (d + 1) → ℝ) → ℝ) (hf : Measurable f) :
    weakLaw d η y {z | f (shiftAdv d η y (Matrix.vecCons a z)) = t}
      = weakLaw d η (-y) {z | f (Matrix.vecCons a z) = t} := by
  rw [← shift_map d η y (-2 * η * y) rfl]
  have hm : MeasurableSet {z : Fin d → ℝ | f (Matrix.vecCons a z) = t} :=
    (hf.comp (meas_vecCons' a)) (measurableSet_singleton t)
  rw [Measure.map_apply (measurable_pi_lambda _ (fun i => (measurable_pi_apply i).add_const _)) hm]
  congr 1
  ext z
  simp [shiftAdv_vecCons]

lemma compl_real (d : ℕ) (η y a : ℝ) (f : (Fin (d + 1) → ℝ) → ℝ) (hf : Measurable f)
    (hpm : ∀ x, f x = 1 ∨ f x = -1) :
    (weakLaw d η y {z | f (Matrix.vecCons a z) = -1}).toReal
      = 1 - (weakLaw d η y {z | f (Matrix.vecCons a z) = 1}).toReal := by
  have hm : MeasurableSet {z : Fin d → ℝ | f (Matrix.vecCons a z) = 1} :=
    (hf.comp (meas_vecCons' a)) (measurableSet_singleton 1)
  have hset : {z : Fin d → ℝ | f (Matrix.vecCons a z) = -1}
      = {z : Fin d → ℝ | f (Matrix.vecCons a z) = 1}ᶜ := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    rcases hpm (Matrix.vecCons a z) with h | h <;> rw [h] <;> norm_num
  rw [hset, prob_compl_eq_one_sub hm, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
    ENNReal.toReal_one]

lemma condLaw_real (d : ℕ) (p η y : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {S : Set (Fin (d+1) → ℝ)}
    (hS : MeasurableSet S) :
    (condLaw d p η y S).toReal = p * (weakLaw d η y {z | Matrix.vecCons y z ∈ S}).toReal
      + (1 - p) * (weakLaw d η y {z | Matrix.vecCons (-y) z ∈ S}).toReal := by
  rw [condLaw_apply d p η y hS, ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hp0,
    ENNReal.toReal_ofReal (by linarith)]

instance (d : ℕ) (p η y : ℝ) : IsFiniteMeasure (condLaw d p η y) := by
  constructor
  rw [condLaw_apply d p η y MeasurableSet.univ]
  finiteness

lemma robust_le (d : ℕ) (p η y ε : ℝ) (hη : 0 ≤ η) (hε : 2 * η ≤ ε) (hy : |y| = 1)
    (f : (Fin (d + 1) → ℝ) → ℝ) (hf : Measurable f) :
    (condLaw d p η y {x | ∀ δ : Fin (d + 1) → ℝ, ‖δ‖ ≤ ε → f (x + δ) = y}).toReal
      ≤ (condLaw d p η y {x | f (shiftAdv d η y x) = y}).toReal := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  have hv : ‖(Matrix.vecCons 0 (fun _ => 1) : Fin (d + 1) → ℝ)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun i => ?_)
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have := hx (-((2 * η * y) • Matrix.vecCons 0 (fun _ => 1)))
    (by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, hy, abs_of_nonneg hη]
      norm_num
      nlinarith)
  rw [← sub_eq_add_neg] at this
  exact this

lemma arith (p δ a b c e : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p < 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hacc : 1 - δ ≤ 1 / 2 * (p * a + (1 - p) * b) + 1 / 2 * (p * (1 - c) + (1 - p) * (1 - e))) :
    1 / 2 * (p * e + (1 - p) * c) + 1 / 2 * (p * (1 - b) + (1 - p) * (1 - a)) ≤ p / (1 - p) * δ := by
  have key : (1 / 2 * (p * e + (1 - p) * c) + 1 / 2 * (p * (1 - b) + (1 - p) * (1 - a))) * (1 - p)
      ≤ p * δ := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * p - 1) (by linarith : (0:ℝ) ≤ 1 - a + c)]
  have h1p : 0 < 1 - p := by linarith
  calc _ ≤ p * δ / (1 - p) := by rw [le_div_iff₀ h1p]; exact key
    _ = p / (1 - p) * δ := by ring

end RRAux_RT

open RobustOdds.Tradeoff in
theorem solution (d : ℕ) (p η ε δ : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p < 1) (hη : 0 ≤ η)
    (hε : 2 * η ≤ ε) (f : (Fin (d + 1) → ℝ) → ℝ) (hf : Measurable f)
    (hpm : ∀ x, f x = 1 ∨ f x = -1) (hacc : 1 - δ ≤ stdAcc d p η f) :
    robustAcc d p η f ε ≤ p / (1 - p) * δ := by
  have hp0 : 0 ≤ p := by linarith
  have hp1' : p ≤ 1 := hp1.le
  have hS : ∀ t : ℝ, MeasurableSet {x : Fin (d + 1) → ℝ | f x = t} :=
    fun t => hf (measurableSet_singleton t)
  have hSh : ∀ y t : ℝ, MeasurableSet {x : Fin (d + 1) → ℝ | f (shiftAdv d η y x) = t} :=
    fun y t => (hf.comp (measurable_id.sub_const _)) (measurableSet_singleton t)
  have r1 := RRAux_RT.robust_le d p η 1 ε hη hε (by norm_num) f hf
  have r2 := RRAux_RT.robust_le d p η (-1) ε hη hε (by norm_num) f hf
  have hrob : robustAcc d p η f ε ≤ shiftAcc d p η f := by
    unfold robustAcc shiftAcc; linarith
  refine hrob.trans ?_
  unfold shiftAcc
  unfold stdAcc at hacc
  rw [RRAux_RT.condLaw_real d p η 1 hp0 hp1' (hSh 1 1),
    RRAux_RT.condLaw_real d p η (-1) hp0 hp1' (hSh (-1) (-1))]
  rw [RRAux_RT.condLaw_real d p η 1 hp0 hp1' (hS 1),
    RRAux_RT.condLaw_real d p η (-1) hp0 hp1' (hS (-1))] at hacc
  simp only [Set.mem_ofPred_eq, neg_neg] at hacc ⊢
  simp only [RRAux_RT.shift_set d η _ _ _ f hf, neg_neg]
  simp only [RRAux_RT.compl_real d η _ _ f hf hpm] at hacc ⊢
  have bnd : ∀ y a : ℝ, 0 ≤ (weakLaw d η y {z | f (Matrix.vecCons a z) = 1}).toReal ∧
      (weakLaw d η y {z | f (Matrix.vecCons a z) = 1}).toReal ≤ 1 :=
    fun y a => ⟨ENNReal.toReal_nonneg, by
      rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one⟩
  exact RRAux_RT.arith p δ _ _ _ _ hp hp1 (bnd 1 1).1 (bnd 1 1).2 (bnd 1 (-1)).1 (bnd 1 (-1)).2
    (bnd (-1) (-1)).1 (bnd (-1) (-1)).2 (bnd (-1) 1).1 (bnd (-1) 1).2 hacc

#print axioms solution
