-- Prove2me | solution 1 for RobustOdds.Tradeoff.shiftAcc_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:04:31.655252+00:00
-- url     : https://prove2.me/submissions/3d052435-bfa8-476c-a9c9-0289c6dacc85

import Mathlib
import Definitions.Def_RobustOdds_Tradeoff_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory RobustOdds.Tradeoff

instance rotFinW (d : ℕ) (η y : ℝ) : IsProbabilityMeasure (weakLaw d η y) := by
  unfold weakLaw; infer_instance

lemma rot_measurable_cons {d : ℕ} (i : ℝ) :
    Measurable (fun z : Fin d → ℝ => (Matrix.vecCons i z : Fin (d + 1) → ℝ)) := by
  refine measurable_pi_lambda _ (fun j => ?_)
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa using measurable_const
  · simpa using measurable_pi_apply k

lemma rot_measurable_cons2 {d : ℕ} :
    Measurable (fun q : ℝ × (Fin d → ℝ) => (Matrix.vecCons q.1 q.2 : Fin (d + 1) → ℝ)) := by
  refine measurable_pi_lambda _ (fun j => ?_)
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [Matrix.cons_val_zero]; exact measurable_fst
  · simp only [Matrix.cons_val_succ]; exact (measurable_pi_apply k).comp measurable_snd

lemma rot_condLaw_apply (d : ℕ) (p η y : ℝ) (S : Set (Fin (d + 1) → ℝ)) (hS : MeasurableSet S) :
    condLaw d p η y S = ENNReal.ofReal p * weakLaw d η y {z | (Matrix.vecCons y z : Fin (d + 1) → ℝ) ∈ S} +
      ENNReal.ofReal (1 - p) * weakLaw d η y {z | (Matrix.vecCons (-y) z : Fin (d + 1) → ℝ) ∈ S} := by
  unfold condLaw
  rw [Measure.map_apply rot_measurable_cons2 hS]
  have hm : MeasurableSet ((fun q : ℝ × (Fin d → ℝ) => (Matrix.vecCons q.1 q.2 : Fin (d + 1) → ℝ)) ⁻¹' S) :=
    rot_measurable_cons2 hS
  rw [Measure.prod_apply hm]
  have hm2 : Measurable (fun x : ℝ => weakLaw d η y (Prod.mk x ⁻¹'
      ((fun q : ℝ × (Fin d → ℝ) => (Matrix.vecCons q.1 q.2 : Fin (d + 1) → ℝ)) ⁻¹' S))) :=
    measurable_measure_prodMk_left hm
  unfold x1Law
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac' _ hm2, lintegral_dirac' _ hm2]
  rfl

lemma rot_condLaw_toReal (d : ℕ) (p η y : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Set (Fin (d + 1) → ℝ)) (hS : MeasurableSet S) :
    (condLaw d p η y S).toReal =
      p * (weakLaw d η y {z | (Matrix.vecCons y z : Fin (d + 1) → ℝ) ∈ S}).toReal +
        (1 - p) * (weakLaw d η y {z | (Matrix.vecCons (-y) z : Fin (d + 1) → ℝ) ∈ S}).toReal := by
  rw [rot_condLaw_apply d p η y S hS,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hp0,
    ENNReal.toReal_ofReal (by linarith)]

lemma rot_neg_toReal (d : ℕ) (η j i : ℝ) (f : (Fin (d + 1) → ℝ) → ℝ) (hf : Measurable f)
    (hpm : ∀ x, f x = 1 ∨ f x = -1) :
    (weakLaw d η j {z | f (Matrix.vecCons i z) = -1}).toReal = 1 - pij d η f i j := by
  have hset : {z : Fin d → ℝ | f (Matrix.vecCons i z) = -1} = {z | f (Matrix.vecCons i z) = 1}ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    rcases hpm (Matrix.vecCons i z) with h | h <;> rw [h] <;> norm_num
  have hmeas : MeasurableSet {z : Fin d → ℝ | f (Matrix.vecCons i z) = 1} :=
    (hf.comp (rot_measurable_cons i)) (measurableSet_singleton (1 : ℝ))
  rw [hset, prob_compl_eq_one_sub hmeas, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
  simp [pij]

lemma rot_weakLaw_shift (d : ℕ) (η : ℝ) :
    ∀ y : ℝ, (weakLaw d η y).map (fun z i => z i - 2 * η * y) = weakLaw d η (-y) := by
  intro y
  unfold weakLaw
  have := Measure.pi_map_pi (μ := fun _ : Fin d => gaussianReal (y * η) 1)
    (f := fun _ (t : ℝ) => t - 2 * η * y) (fun i => by fun_prop)
  rw [this]
  simp only [gaussianReal_map_sub_const]
  congr 1
  funext i
  congr 1
  ring

lemma rot_shiftAdv_cons (d : ℕ) (η y i : ℝ) (z : Fin d → ℝ) :
    shiftAdv d η y (Matrix.vecCons i z : Fin (d + 1) → ℝ) =
      Matrix.vecCons i (fun k => z k - 2 * η * y) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [shiftAdv]
  · simp [shiftAdv]

lemma rot_shift_set (d : ℕ) (η y i s : ℝ) (f : (Fin (d + 1) → ℝ) → ℝ) (hf : Measurable f) :
    (weakLaw d η y {z | f (shiftAdv d η y (Matrix.vecCons i z : Fin (d + 1) → ℝ)) = s}) =
      weakLaw d η (-y) {z | f (Matrix.vecCons i z : Fin (d + 1) → ℝ) = s} := by
  have hmeas : MeasurableSet {z : Fin d → ℝ | f (Matrix.vecCons i z : Fin (d + 1) → ℝ) = s} :=
    (hf.comp (rot_measurable_cons i)) (measurableSet_singleton s)
  have hT : Measurable (fun (z : Fin d → ℝ) (k : Fin d) => z k - 2 * η * y) := by fun_prop
  rw [← rot_weakLaw_shift d η y, Measure.map_apply hT hmeas]
  simp only [rot_shiftAdv_cons]
  rfl

theorem solution (d : ℕ) (p η : ℝ) (hp : 1 / 2 ≤ p) (hp1' : p ≤ 1)
    (f : (Fin (d + 1) → ℝ) → ℝ) (hf : Measurable f) (hpm : ∀ x, f x = 1 ∨ f x = -1) :
    shiftAcc d p η f = 1 / 2 * (p * (1 + pij d η f 1 (-1) - pij d η f (-1) 1) +
      (1 - p) * (1 + pij d η f (-1) (-1) - pij d η f 1 1)) := by
  have hp0 : 0 ≤ p := by linarith
  have hsh : ∀ y : ℝ, Measurable (shiftAdv d η y) := fun y => by unfold shiftAdv; fun_prop
  have h1 : MeasurableSet {x : Fin (d + 1) → ℝ | f (shiftAdv d η 1 x) = 1} :=
    (hf.comp (hsh 1)) (measurableSet_singleton (1 : ℝ))
  have h2 : MeasurableSet {x : Fin (d + 1) → ℝ | f (shiftAdv d η (-1) x) = -1} :=
    (hf.comp (hsh (-1))) (measurableSet_singleton (-1 : ℝ))
  unfold shiftAcc
  rw [rot_condLaw_toReal d p η 1 hp0 hp1' _ h1, rot_condLaw_toReal d p η (-1) hp0 hp1' _ h2]
  simp only [Set.mem_setOf_eq, neg_neg]
  rw [rot_shift_set d η 1 1 1 f hf, rot_shift_set d η 1 (-1) 1 f hf,
    rot_shift_set d η (-1) (-1) (-1) f hf, rot_shift_set d η (-1) 1 (-1) f hf]
  simp only [neg_neg]
  rw [rot_neg_toReal d η 1 (-1) f hf hpm, rot_neg_toReal d η 1 1 f hf hpm]
  simp only [pij]
  ring
