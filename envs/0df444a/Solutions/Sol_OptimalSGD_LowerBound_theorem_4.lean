-- Prove2me | solution 1 for OptimalSGD.LowerBound.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T15:34:01.514725+00:00
-- url     : https://prove2.me/submissions/0115fdba-96f6-4d3c-b474-7488130fc4c7

import Mathlib
import Definitions.Def_UnderstandingML_Framework
import Definitions.Def_UnderstandingML_Linear
import Definitions.Def_OptimalSGD_LowerBound_Model

set_option autoImplicit false

namespace SGDB4

open MeasureTheory UnderstandingML OptimalSGD.LowerBound

/-- Scalar recursion followed by the first coordinate of `runB`. -/
noncomputable def xs (c x0 : ℝ) (Z : ℕ → ℝ) : ℕ → ℝ
  | 0 => x0
  | k + 1 => max (-1) (min 1 (xs c x0 Z k - (c / ((k : ℝ) + 1)) *
      (xs c x0 Z k + (if 0 ≤ xs c x0 Z k then Z k else -7))))

lemma xs_succ (c x0 : ℝ) (Z : ℕ → ℝ) (k : ℕ) :
    xs c x0 Z (k + 1) = max (-1) (min 1 (xs c x0 Z k - (c / ((k : ℝ) + 1)) *
      (xs c x0 Z k + (if 0 ≤ xs c x0 Z k then Z k else -7)))) := rfl

lemma runB_zero {d : ℕ} [NeZero d] (c : ℝ) (w₁ : Vec d) (Z : ℕ → ℝ) (k : ℕ) :
    (runB c w₁ Z k) 0 = xs c (w₁ 0) Z k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [xs_succ, ← ih]
    simp [runB, sgdRun, boxProj, oracleB]
    by_cases h : 0 ≤ (sgdRun (boxProj (-1) 1) oracleB c w₁ Z k) 0 <;>
      simp only [h, if_true, if_false] <;> ring_nf

lemma xs_congr (c x0 : ℝ) (Z Z' : ℕ → ℝ) (k : ℕ) (h : ∀ j < k, Z j = Z' j) :
    xs c x0 Z k = xs c x0 Z' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [xs_succ, xs_succ, ih (fun j hj => h j (by omega)), h k (by omega)]

lemma xs_mem (c x0 : ℝ) (Z : ℕ → ℝ) (hx0 : x0 ∈ Set.Icc (-1 : ℝ) 1) (k : ℕ) :
    xs c x0 Z k ∈ Set.Icc (-1 : ℝ) 1 := by
  cases k with
  | zero => exact hx0
  | succ k =>
    rw [xs_succ]
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)

/-- Pathwise sign facts: after a negative iterate the next one is positive, and every iterate
is at least `-3 c / k`. -/
lemma xs_sign (c x0 : ℝ) (hc : 0 < c) (Z : ℕ → ℝ) (hZ : ∀ j, Z j ∈ Set.Icc (-1 : ℝ) 3)
    (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) :
    (- (3 * c / ((k : ℝ) + 1)) ≤ xs c x0 Z (k + 1)) ∧
      (xs c x0 Z k < 0 → 0 < xs c x0 Z (k + 1)) := by
  have hmem : ∀ j, xs c x0 Z j ∈ Set.Icc (-1 : ℝ) 1 :=
    xs_mem c x0 Z ⟨by linarith [hx0.1], hx0.2⟩
  induction k with
  | zero =>
    have h0 : xs c x0 Z 0 = x0 := rfl
    have hz := hZ 0
    refine ⟨?_, fun h => by rw [h0] at h; linarith [hx0.1]⟩
    rw [xs_succ, h0, if_pos hx0.1]
    simp only [Nat.cast_zero, zero_add, div_one]
    rcases le_or_gt (3 * c) 1 with hc1 | hc1
    · refine le_max_of_le_right (le_min (by linarith) ?_)
      nlinarith [hx0.1, hx0.2, hz.1, hz.2]
    · exact le_max_of_le_left (by linarith)
  | succ k ih =>
    set x := xs c x0 Z (k + 1) with hx
    have hxm := hmem (k + 1)
    have hz := hZ (k + 1)
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hk2 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + 1 := by positivity
    have hpos : x < 0 → 0 < xs c x0 Z (k + 1 + 1) := by
      intro hneg
      rw [xs_succ, ← hx, if_neg (not_le.mpr hneg)]
      have hlow := ih.1
      rw [hx] at hlow
      have ha : 0 < c / (((k + 1 : ℕ) : ℝ) + 1) := div_pos hc hk2
      refine lt_of_lt_of_le ?_ (le_max_right _ _)
      refine lt_min (by norm_num) ?_
      -- x - a (x - 7) = (1 - a) x + 7 a with x ≥ -3c/(k+1), a = c/(k+2)
      have key : 0 < x - c / (((k + 1 : ℕ) : ℝ) + 1) * (x + -7) := by
        rcases le_or_gt (c / (((k + 1 : ℕ) : ℝ) + 1)) 1 with ha1 | ha1
        · have h3 : 3 * c / ((k : ℝ) + 1) < 7 * (c / (((k + 1 : ℕ) : ℝ) + 1)) := by
            rw [show (7:ℝ) * (c / (((k + 1 : ℕ) : ℝ) + 1)) = 7 * c / ((k:ℝ) + 2) by push_cast; ring]
            rw [div_lt_div_iff₀ hk (by positivity)]
            nlinarith
          nlinarith
        · nlinarith
      exact key
    refine ⟨?_, hpos⟩
    rcases le_or_gt 0 x with hx0' | hneg
    · rw [xs_succ, ← hx, if_pos hx0']
      have ha : 0 < c / (((k + 1 : ℕ) : ℝ) + 1) := div_pos hc hk2
      have e : 3 * c / (((k + 1 : ℕ) : ℝ) + 1) = 3 * (c / (((k + 1 : ℕ) : ℝ) + 1)) := by ring
      rw [e]
      rcases le_or_gt (3 * (c / (((k + 1 : ℕ) : ℝ) + 1))) 1 with ha1 | ha1
      · refine le_max_of_le_right (le_min (by linarith) ?_)
        have h1a : 0 ≤ 1 - c / (((k + 1 : ℕ) : ℝ) + 1) := by linarith
        nlinarith [mul_nonneg h1a hx0', mul_nonneg ha.le (sub_nonneg.2 hz.2)]
      · exact le_max_of_le_left (by linarith)
    · have := hpos hneg
      have : 0 < 3 * c / (((k + 1 : ℕ) : ℝ) + 1) := by positivity
      linarith

/-! ### Measure-theoretic infrastructure -/

instance noiseLaw_isProb : IsProbabilityMeasure noiseLaw := by
  unfold noiseLaw
  exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite (by norm_num [Real.volume_Icc])
    (by simp [Real.volume_Icc])

lemma noise_ae : ∀ᵐ z ∂noiseLaw, z ∈ Set.Icc (-1 : ℝ) 3 := by
  unfold noiseLaw ProbabilityTheory.cond
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

lemma noise_mean : ∫ z, z ∂noiseLaw = 1 := by
  unfold noiseLaw ProbabilityTheory.cond
  rw [integral_smul_measure, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
    (by norm_num), integral_id, Real.volume_Icc]
  norm_num [ENNReal.toReal_inv, ENNReal.toReal_ofReal]

lemma iid_ae (T : ℕ) : ∀ᵐ Z ∂(iidLaw noiseLaw T), ∀ i, Z i ∈ Set.Icc (-1 : ℝ) 3 := by
  rw [ae_all_iff]
  intro i
  have hmp := measurePreserving_eval (fun _ : Fin T => noiseLaw) i
  refine ae_of_ae_map (measurable_pi_apply i).aemeasurable ?_
  unfold iidLaw
  rw [hmp.map_eq]
  exact noise_ae

lemma measurable_extendNoise (T : ℕ) : Measurable (fun Z : Fin T → ℝ => extendNoise Z) := by
  refine measurable_pi_lambda _ (fun j => ?_)
  unfold extendNoise
  by_cases h : j < T
  · simp only [h, dif_pos]; exact measurable_pi_apply _
  · simp only [h, dif_neg, not_false_eq_true]; exact measurable_const

lemma measurable_xs (c x0 : ℝ) (k : ℕ) : Measurable (fun Z : ℕ → ℝ => xs c x0 Z k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    simp only [xs_succ]
    have hite : Measurable (fun Z : ℕ → ℝ => if 0 ≤ xs c x0 Z k then Z k else -7) :=
      Measurable.ite (measurableSet_le measurable_const ih) (measurable_pi_apply k) measurable_const
    exact measurable_const.max (measurable_const.min (ih.sub (measurable_const.mul (ih.add hite))))

/-- Independence: the noise `Z_k` is independent of anything built from `Z_0, …, Z_{k-1}`,
and has mean `1`. -/
lemma indep_mul {T k : ℕ} (hk : k < T) (f : (ℕ → ℝ) → ℝ) (hf : Measurable f)
    (hdep : ∀ Z Z' : ℕ → ℝ, (∀ j < k, Z j = Z' j) → f Z = f Z') :
    ∫ Z, f (extendNoise Z) * Z ⟨k, hk⟩ ∂(iidLaw noiseLaw T) =
      ∫ Z, f (extendNoise Z) ∂(iidLaw noiseLaw T) := by
  have hind : ProbabilityTheory.iIndepFun (fun i (ω : Fin T → ℝ) => ω i) (iidLaw noiseLaw T) :=
    ProbabilityTheory.iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id)
  let S : Finset (Fin T) := Finset.univ.filter (fun i => i.val < k)
  let U : Finset (Fin T) := {⟨k, hk⟩}
  have hdisj : Disjoint S U := by
    simp [S, U, Finset.disjoint_singleton_right]
  have hI := hind.indepFun_finset S U hdisj (fun i => measurable_pi_apply i)
  let g : (S → ℝ) → ℝ := fun y => f (fun j => if h : j < k then
    y ⟨⟨j, by omega⟩, by simp [S, h]⟩ else 0)
  have hg : Measurable g := by
    refine hf.comp (measurable_pi_lambda _ (fun j => ?_))
    by_cases h : j < k
    · simp only [h, dif_pos]; exact measurable_pi_apply _
    · simp only [h, dif_neg, not_false_eq_true]; exact measurable_const
  let h2 : (U → ℝ) → ℝ := fun y => y ⟨⟨k, hk⟩, Finset.mem_singleton_self _⟩
  have hI2 := hI.comp hg (measurable_pi_apply _ : Measurable h2)
  have hfg : ∀ Z : Fin T → ℝ, f (extendNoise Z) = g (fun i : S => Z i) := by
    intro Z
    apply hdep
    intro j hj
    simp [extendNoise, hj, show j < T by omega]
  have e1 : (fun Z : Fin T → ℝ => f (extendNoise Z) * Z ⟨k, hk⟩) =
      fun Z => (g ∘ fun a (i : S) => a i) Z * (h2 ∘ fun a (i : U) => a i) Z := by
    funext Z; simp [hfg, h2]
  have e2 : (fun Z : Fin T → ℝ => f (extendNoise Z)) = fun Z => (g ∘ fun a (i : S) => a i) Z := by
    funext Z; simp [hfg]
  rw [e1, e2, hI2.integral_fun_mul_eq_mul_integral]
  · have : ∫ Z, (h2 ∘ fun a (i : U) => a i) Z ∂(iidLaw noiseLaw T) = 1 := by
      show ∫ Z : Fin T → ℝ, Z ⟨k, hk⟩ ∂(Measure.pi fun _ => noiseLaw) = 1
      have h := integral_comp_eval (μ := fun _ : Fin T => noiseLaw) (i := ⟨k, hk⟩) (f := id)
        aestronglyMeasurable_id
      simp only [id] at h
      rw [h]
      exact noise_mean
    rw [this, mul_one]
  · exact (hg.comp (measurable_pi_lambda _ (fun i => measurable_pi_apply _))).aestronglyMeasurable
  · exact ((measurable_pi_apply _).comp
      (measurable_pi_lambda _ (fun i => measurable_pi_apply _))).aestronglyMeasurable

/-! ### The objective and integrability -/

lemma runB_succ_apply {d : ℕ} [NeZero d] (c : ℝ) (w₁ : Vec d) (Z : ℕ → ℝ) (k : ℕ) (i : Fin d) :
    (runB c w₁ Z (k + 1)) i = max (-1) (min 1 ((runB c w₁ Z k) i - (c / ((k : ℝ) + 1)) *
      ((runB c w₁ Z k) i + (if i = 0 then (if 0 ≤ (runB c w₁ Z k) 0 then Z k else -7) else 0)))) := by
  simp only [runB, sgdRun, boxProj, oracleB]
  by_cases hi : i = 0
  · subst hi
    by_cases h : 0 ≤ (sgdRun (boxProj (-1) 1) oracleB c w₁ Z k) 0 <;>
      simp [h] <;> ring_nf
  · simp [hi]

lemma runB_mem {d : ℕ} [NeZero d] (c : ℝ) (w₁ : Vec d) (hw₁ : w₁ ∈ box (-1) 1) (Z : ℕ → ℝ)
    (k : ℕ) (i : Fin d) : (runB c w₁ Z k) i ∈ Set.Icc (-1 : ℝ) 1 := by
  cases k with
  | zero => exact hw₁ i
  | succ k =>
    rw [runB_succ_apply]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma measurable_vec {d : ℕ} {α : Type*} [MeasurableSpace α] {F : α → Vec d}
    (h : ∀ i, Measurable fun a => F a i) : Measurable F := by
  have e : F = fun a => (MeasurableEquiv.toLp 2 (Fin d → ℝ)) (fun i => F a i) := by
    funext a; rfl
  rw [e]
  exact (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp (measurable_pi_lambda _ h)

lemma measurable_runB {d : ℕ} [NeZero d] (c : ℝ) (w₁ : Vec d) (k : ℕ) (i : Fin d) :
    Measurable (fun Z : ℕ → ℝ => (runB c w₁ Z k) i) := by
  induction k generalizing i with
  | zero => change Measurable (fun _ : ℕ → ℝ => w₁ i); exact measurable_const
  | succ k ih =>
    simp only [runB_succ_apply]
    have hite : Measurable (fun Z : ℕ → ℝ => if i = 0 then
        (if 0 ≤ (runB c w₁ Z k) 0 then Z k else -7) else 0) := by
      by_cases hi : i = 0
      · simp only [hi, if_true]
        exact Measurable.ite (measurableSet_le measurable_const (ih 0)) (measurable_pi_apply k)
          measurable_const
      · simp only [hi, if_false]; exact measurable_const
    exact measurable_const.max (measurable_const.min ((ih i).sub
      (measurable_const.mul ((ih i).add hite))))

lemma avgB_apply {d : ℕ} [NeZero d] (c : ℝ) (w₁ : Vec d) {T : ℕ} (Z : Fin T → ℝ) (i : Fin d) :
    (avgB c w₁ Z) i = (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (runB c w₁ (extendNoise Z) t) i := by
  simp [avgB]

lemma measurable_objB_avgB {d : ℕ} [NeZero d] (c : ℝ) (w₁ : Vec d) (T : ℕ) :
    Measurable (fun Z : Fin T → ℝ => objB (avgB c w₁ Z)) := by
  have hav : Measurable (fun Z : Fin T → ℝ => avgB c w₁ Z) := by
    refine measurable_vec (fun i => ?_)
    simp only [avgB_apply]
    refine measurable_const.mul (Finset.measurable_sum _ (fun t _ => ?_))
    exact (measurable_runB c w₁ t i).comp (measurable_extendNoise T)
  have h0 : Measurable (fun w : Vec d => w 0) := (measurable_pi_apply 0).comp
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurable
  have hobj : Measurable (fun w : Vec d => objB w) := by
    unfold objB
    exact (measurable_const.mul (continuous_norm.measurable.pow_const 2)).add
      (Measurable.ite (measurableSet_le measurable_const h0) h0 (measurable_const.mul h0))
  exact hobj.comp hav

lemma objB_zero' {d : ℕ} [NeZero d] : objB (0 : Vec d) = 0 := by
  simp [objB]

lemma objB_ge {d : ℕ} [NeZero d] (w : Vec d) : w 0 ≤ objB w ∧ 0 ≤ objB w := by
  unfold objB
  have hn : 0 ≤ (1 / 2 : ℝ) * ‖w‖ ^ 2 := by positivity
  split_ifs with h
  · exact ⟨by linarith, by linarith⟩
  · push Not at h
    exact ⟨by linarith, by linarith⟩

/-! ### Pathwise step facts (noise in `[-1, 3]`, start in `[0, 1]`) -/

/-- Indicator of a negative iterate. -/
noncomputable def nn (x : ℝ) : ℝ := if x < 0 then 1 else 0

lemma nn_mem (x : ℝ) : nn x = 0 ∨ nn x = 1 := by
  unfold nn; split_ifs <;> simp

/-- No bottom clamp once `3 a_k ≤ 1`: the drift inequality. -/
lemma step_upper (c x0 : ℝ) (hc : 0 < c) (Z : ℕ → ℝ) (hZ : ∀ j, Z j ∈ Set.Icc (-1 : ℝ) 3)
    (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) (ha : 3 * (c / ((k : ℝ) + 1)) ≤ 1) :
    xs c x0 Z (k + 1) ≤ (1 - c / ((k : ℝ) + 1)) * xs c x0 Z k
      - c / ((k : ℝ) + 1) * Z k * (1 - nn (xs c x0 Z k))
      + 7 * (c / ((k : ℝ) + 1)) * nn (xs c x0 Z k) := by
  have hm := xs_mem c x0 Z ⟨by linarith [hx0.1], hx0.2⟩ k
  have hz := hZ k
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hapos : 0 < c / ((k : ℝ) + 1) := div_pos hc hk
  set a := c / ((k : ℝ) + 1) with ha_def
  set x := xs c x0 Z k with hx
  rw [xs_succ, ← hx, ← ha_def]
  unfold nn
  by_cases h : x < 0
  · rw [if_neg (not_le.mpr h), if_pos h]
    refine max_le (by nlinarith [hm.1]) (le_trans (min_le_right _ _) (by linarith))
  · rw [if_pos (not_lt.mp h), if_neg h]
    refine max_le ?_ (le_trans (min_le_right _ _) (by linarith))
    have h1a : 0 ≤ 1 - a := by linarith
    nlinarith [mul_nonneg h1a (not_lt.mp h), mul_nonneg hapos.le (sub_nonneg.2 hz.2)]

/-- After a negative iterate the next one is at least `min 1 (7 a_k − 3 a_{k−1} (1 − a_k))`. -/
lemma neg_next_lower (c x0 : ℝ) (hc : 0 < c) (Z : ℕ → ℝ) (hZ : ∀ j, Z j ∈ Set.Icc (-1 : ℝ) 3)
    (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) (ha : c / ((j : ℝ) + 2) ≤ 1)
    (hneg : xs c x0 Z (j + 1) < 0) :
    min 1 (7 * (c / ((j : ℝ) + 2)) - 3 * (c / ((j : ℝ) + 1)) * (1 - c / ((j : ℝ) + 2)))
      ≤ xs c x0 Z (j + 1 + 1) := by
  have hlow := (xs_sign c x0 hc Z hZ hx0 j).1
  have hk : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have e1 : ((j + 1 : ℕ) : ℝ) + 1 = (j : ℝ) + 2 := by push_cast; ring
  rw [xs_succ, if_neg (not_le.mpr hneg), e1]
  set a := c / ((j : ℝ) + 2)
  set x := xs c x0 Z (j + 1)
  have h3 : 3 * c / ((j : ℝ) + 1) = 3 * (c / ((j : ℝ) + 1)) := by ring
  rw [h3] at hlow
  refine le_max_of_le_right (min_le_min le_rfl ?_)
  have h1a : 0 ≤ 1 - a := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hlow h1a]

/-- Two steps after a negative iterate there is no clamping. -/
lemma neg_next2 (c x0 : ℝ) (hc : 0 < c) (Z : ℕ → ℝ) (hZ : ∀ j, Z j ∈ Set.Icc (-1 : ℝ) 3)
    (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) (ha : 3 * (c / ((k : ℝ) + 2)) ≤ 1)
    (hneg : xs c x0 Z k < 0) :
    xs c x0 Z (k + 2) = (1 - c / ((k : ℝ) + 2)) * xs c x0 Z (k + 1)
      - c / ((k : ℝ) + 2) * Z (k + 1) := by
  have hpos := (xs_sign c x0 hc Z hZ hx0 k).2 hneg
  have hm := xs_mem c x0 Z ⟨by linarith [hx0.1], hx0.2⟩ (k + 1)
  have hz := hZ (k + 1)
  have e1 : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
  have hapos : 0 < c / ((k : ℝ) + 2) := div_pos hc (by positivity)
  rw [show k + 2 = k + 1 + 1 from rfl, xs_succ, if_pos hpos.le, e1]
  set a := c / ((k : ℝ) + 2)
  set x := xs c x0 Z (k + 1)
  have h1a : 0 ≤ 1 - a := by linarith
  have hv1 : x - a * (x + Z (k + 1)) ≤ 1 := by nlinarith [hm.2, hz.1]
  have hv2 : -1 ≤ x - a * (x + Z (k + 1)) := by
    nlinarith [mul_nonneg h1a hpos.le, mul_nonneg hapos.le (sub_nonneg.2 hz.2)]
  rw [min_eq_right hv1, max_eq_right hv2]
  ring

lemma block0 (x : ℝ) : nn x * x ≤ x := by
  unfold nn; split_ifs with h <;> linarith

lemma block1 (c x0 : ℝ) (hc : 0 < c) (Z : ℕ → ℝ) (hZ : ∀ j, Z j ∈ Set.Icc (-1 : ℝ) 3)
    (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (u : ℕ) :
    nn (xs c x0 Z (u + 1)) * xs c x0 Z (u + 1) + nn (xs c x0 Z u) * xs c x0 Z (u + 1)
      ≤ xs c x0 Z (u + 1) := by
  have h1 := (xs_sign c x0 hc Z hZ hx0 u).2
  unfold nn
  by_cases hu : xs c x0 Z u < 0
  · have := h1 hu
    rw [if_neg (not_lt.mpr this.le), if_pos hu]; linarith
  · rw [if_neg hu]; split_ifs <;> linarith

lemma block2 (c x0 : ℝ) (hc : 0 < c) (Z : ℕ → ℝ) (hZ : ∀ j, Z j ∈ Set.Icc (-1 : ℝ) 3)
    (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (u : ℕ) :
    nn (xs c x0 Z (u + 2)) * xs c x0 Z (u + 2) + nn (xs c x0 Z (u + 1)) * xs c x0 Z (u + 2)
      + nn (xs c x0 Z u) * xs c x0 Z (u + 2) ≤ xs c x0 Z (u + 2) := by
  have h1 := (xs_sign c x0 hc Z hZ hx0 u).2
  have h2 := (xs_sign c x0 hc Z hZ hx0 (u + 1)).2
  unfold nn
  by_cases hu1 : xs c x0 Z (u + 1) < 0
  · have hp := h2 hu1
    have hu : ¬ xs c x0 Z u < 0 := fun h => by linarith [h1 h]
    rw [if_neg (not_lt.mpr hp.le), if_pos hu1, if_neg hu]; linarith
  · rw [if_neg hu1]
    by_cases hu : xs c x0 Z u < 0
    · rw [if_pos hu]; split_ifs <;> linarith
    · rw [if_neg hu]; split_ifs <;> linarith

/-! ### Expectation facts -/

instance iidLaw_isProb (T : ℕ) : IsProbabilityMeasure (iidLaw noiseLaw T) := by
  unfold iidLaw; infer_instance

/-- The scalar iterate as a function of the noise vector. -/
noncomputable def X (c x0 : ℝ) (T : ℕ) (k : ℕ) (Z : Fin T → ℝ) : ℝ := xs c x0 (extendNoise Z) k

lemma measurable_X (c x0 : ℝ) (T k : ℕ) : Measurable (X c x0 T k) :=
  (measurable_xs c x0 k).comp (measurable_extendNoise T)

lemma measurable_nn {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f) :
    Measurable (fun a => nn (f a)) :=
  Measurable.ite (measurableSet_lt hf measurable_const) measurable_const measurable_const

lemma abs_nn_le (x : ℝ) : |nn x| ≤ 1 := by
  unfold nn; split_ifs <;> norm_num

lemma ae_ext (T : ℕ) :
    ∀ᵐ Z ∂(iidLaw noiseLaw T), ∀ j, extendNoise Z j ∈ Set.Icc (-1 : ℝ) 3 := by
  filter_upwards [iid_ae T] with Z hZ j
  unfold extendNoise
  split_ifs
  · exact hZ _
  · norm_num

lemma integ_bdd {T : ℕ} {f : (Fin T → ℝ) → ℝ} (hf : Measurable f) (C : ℝ)
    (h : ∀ᵐ Z ∂(iidLaw noiseLaw T), |f Z| ≤ C) : Integrable f (iidLaw noiseLaw T) :=
  Integrable.of_bound hf.aestronglyMeasurable C (by
    filter_upwards [h] with Z hZ
    simpa [Real.norm_eq_abs] using hZ)

lemma abs_X_le (c x0 : ℝ) (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (T k : ℕ) (Z : Fin T → ℝ) :
    |X c x0 T k Z| ≤ 1 := by
  have := xs_mem c x0 (extendNoise Z) ⟨by linarith [hx0.1], hx0.2⟩ k
  exact abs_le.2 ⟨this.1, this.2⟩

lemma integ_X (c x0 : ℝ) (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (T k : ℕ) :
    Integrable (X c x0 T k) (iidLaw noiseLaw T) :=
  integ_bdd (measurable_X c x0 T k) 1 (Filter.Eventually.of_forall (abs_X_le c x0 hx0 T k))

lemma integ_nn (c x0 : ℝ) (T k : ℕ) :
    Integrable (fun Z => nn (X c x0 T k Z)) (iidLaw noiseLaw T) :=
  integ_bdd (measurable_nn (measurable_X c x0 T k)) 1
    (Filter.Eventually.of_forall (fun Z => abs_nn_le _))

lemma integ_nnX (c x0 : ℝ) (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (T k j : ℕ) :
    Integrable (fun Z => nn (X c x0 T k Z) * X c x0 T j Z) (iidLaw noiseLaw T) :=
  integ_bdd ((measurable_nn (measurable_X c x0 T k)).mul (measurable_X c x0 T j)) 1
    (Filter.Eventually.of_forall (fun Z => by
      rw [abs_mul]
      have := abs_nn_le (X c x0 T k Z)
      have := abs_X_le c x0 hx0 T j Z
      nlinarith [abs_nonneg (nn (X c x0 T k Z)), abs_nonneg (X c x0 T j Z)]))

lemma integ_nnZ (c x0 : ℝ) (T k j : ℕ) (hj : j < T) :
    Integrable (fun Z : Fin T → ℝ => nn (X c x0 T k Z) * Z ⟨j, hj⟩) (iidLaw noiseLaw T) :=
  integ_bdd ((measurable_nn (measurable_X c x0 T k)).mul (measurable_pi_apply _)) 3 (by
    filter_upwards [iid_ae T] with Z hZ
    rw [abs_mul]
    have h1 := abs_nn_le (X c x0 T k Z)
    have h2 : |Z ⟨j, hj⟩| ≤ 3 := abs_le.2 ⟨by linarith [(hZ ⟨j, hj⟩).1], (hZ ⟨j, hj⟩).2⟩
    nlinarith [abs_nonneg (nn (X c x0 T k Z)), abs_nonneg (Z ⟨j, hj⟩)])

lemma integ_Z (T j : ℕ) (hj : j < T) :
    Integrable (fun Z : Fin T → ℝ => Z ⟨j, hj⟩) (iidLaw noiseLaw T) :=
  integ_bdd (measurable_pi_apply _) 3 (by
    filter_upwards [iid_ae T] with Z hZ
    exact abs_le.2 ⟨by linarith [(hZ ⟨j, hj⟩).1], (hZ ⟨j, hj⟩).2⟩)

/-- `E[n_k Z_j] = E[n_k]` for `k ≤ j < T`. -/
lemma int_nnZ (c x0 : ℝ) (T k j : ℕ) (hkj : k ≤ j) (hj : j < T) :
    ∫ Z, nn (X c x0 T k Z) * Z ⟨j, hj⟩ ∂(iidLaw noiseLaw T) =
      ∫ Z, nn (X c x0 T k Z) ∂(iidLaw noiseLaw T) := by
  have := indep_mul hj (fun W => nn (xs c x0 W k)) (measurable_nn (measurable_xs c x0 k))
    (fun W W' h => by rw [xs_congr c x0 W W' k (fun i hi => h i (by omega))])
  simpa [X] using this

lemma extendNoise_lt {T : ℕ} (Z : Fin T → ℝ) (j : ℕ) (hj : j < T) :
    extendNoise Z j = Z ⟨j, hj⟩ := by
  simp [extendNoise, hj]

/-- (E1) drift inequality in expectation. -/
lemma E1 (c x0 : ℝ) (hc : 0 < c) (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (T k : ℕ) (hk : k < T)
    (ha : 3 * (c / ((k : ℝ) + 1)) ≤ 1) :
    ∫ Z, X c x0 T (k + 1) Z ∂(iidLaw noiseLaw T) ≤
      (1 - c / ((k : ℝ) + 1)) * ∫ Z, X c x0 T k Z ∂(iidLaw noiseLaw T) - c / ((k : ℝ) + 1)
        + 8 * (c / ((k : ℝ) + 1)) * ∫ Z, nn (X c x0 T k Z) ∂(iidLaw noiseLaw T) := by
  set a := c / ((k : ℝ) + 1) with ha_def
  have hstep : ∀ᵐ Z ∂(iidLaw noiseLaw T), X c x0 T (k + 1) Z ≤
      ((1 - a) * X c x0 T k Z - a * Z ⟨k, hk⟩) + a * (nn (X c x0 T k Z) * Z ⟨k, hk⟩)
        + 7 * a * nn (X c x0 T k Z) := by
    filter_upwards [ae_ext T] with Z hZ
    have := step_upper c x0 hc (extendNoise Z) hZ hx0 k ha
    rw [extendNoise_lt Z k hk] at this
    exact le_of_le_of_eq this (by simp only [X]; ring)
  have hI1 := integ_X c x0 hx0 T k
  have hI2 := integ_Z T k hk
  have hI3 := integ_nnZ c x0 T k k hk
  have hI4 := integ_nn c x0 T k
  have hE1 : Integrable (fun Z => (1 - a) * X c x0 T k Z) (iidLaw noiseLaw T) := hI1.const_mul _
  have hE2 : Integrable (fun Z : Fin T → ℝ => a * Z ⟨k, hk⟩) (iidLaw noiseLaw T) :=
    hI2.const_mul _
  have hA : Integrable (fun Z : Fin T → ℝ => (1 - a) * X c x0 T k Z - a * Z ⟨k, hk⟩)
      (iidLaw noiseLaw T) := hE1.sub hE2
  have hC : Integrable (fun Z : Fin T → ℝ => a * (nn (X c x0 T k Z) * Z ⟨k, hk⟩))
      (iidLaw noiseLaw T) := hI3.const_mul _
  have hB : Integrable (fun Z : Fin T → ℝ => ((1 - a) * X c x0 T k Z - a * Z ⟨k, hk⟩)
      + a * (nn (X c x0 T k Z) * Z ⟨k, hk⟩)) (iidLaw noiseLaw T) := hA.add hC
  have hD : Integrable (fun Z => 7 * a * nn (X c x0 T k Z)) (iidLaw noiseLaw T) :=
    hI4.const_mul _
  have hIR : Integrable (fun Z : Fin T → ℝ => ((1 - a) * X c x0 T k Z - a * Z ⟨k, hk⟩)
      + a * (nn (X c x0 T k Z) * Z ⟨k, hk⟩) + 7 * a * nn (X c x0 T k Z)) (iidLaw noiseLaw T) :=
    hB.add hD
  have hmono := integral_mono_ae (integ_X c x0 hx0 T (k + 1)) hIR hstep
  rw [integral_add hB hD, integral_add hA hC, integral_sub hE1 hE2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    int_nnZ c x0 T k k le_rfl hk] at hmono
  have hmean : ∫ Z : Fin T → ℝ, Z ⟨k, hk⟩ ∂(iidLaw noiseLaw T) = 1 := by
    have h := integral_comp_eval (μ := fun _ : Fin T => noiseLaw) (i := ⟨k, hk⟩) (f := id)
      aestronglyMeasurable_id
    simp only [id] at h
    unfold iidLaw
    rw [h]
    exact noise_mean
  rw [hmean] at hmono
  linarith

lemma nn_nonneg (x : ℝ) : 0 ≤ nn x := by unfold nn; split_ifs <;> norm_num

lemma nn_le_one (x : ℝ) : nn x ≤ 1 := by unfold nn; split_ifs <;> norm_num

/-- (E2) `E[n_k x_k] ≥ −(3c/(j+1)) E[n_k]` for `k = j + 1`. -/
lemma E2 (c x0 : ℝ) (hc : 0 < c) (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (T j : ℕ) :
    -(3 * c / ((j : ℝ) + 1)) * ∫ Z, nn (X c x0 T (j + 1) Z) ∂(iidLaw noiseLaw T) ≤
      ∫ Z, nn (X c x0 T (j + 1) Z) * X c x0 T (j + 1) Z ∂(iidLaw noiseLaw T) := by
  rw [← integral_const_mul]
  refine integral_mono_ae ((integ_nn c x0 T (j + 1)).const_mul _) (integ_nnX c x0 hx0 T _ _) ?_
  filter_upwards [ae_ext T] with Z hZ
  have h := (xs_sign c x0 hc (extendNoise Z) hZ hx0 j).1
  simp only [X]
  unfold nn
  split_ifs <;> linarith

/-- (E2') `E[x_k] ≥ E[n_k x_k]`. -/
lemma E2' (c x0 : ℝ) (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (T k : ℕ) :
    ∫ Z, nn (X c x0 T k Z) * X c x0 T k Z ∂(iidLaw noiseLaw T) ≤
      ∫ Z, X c x0 T k Z ∂(iidLaw noiseLaw T) :=
  integral_mono (integ_nnX c x0 hx0 T k k) (integ_X c x0 hx0 T k) (fun Z => block0 _)

/-- (E3) after a negative iterate. -/
lemma E3 (c x0 : ℝ) (hc : 0 < c) (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (T j : ℕ)
    (ha : c / ((j : ℝ) + 2) ≤ 1) :
    min 1 (7 * (c / ((j : ℝ) + 2)) - 3 * (c / ((j : ℝ) + 1)) * (1 - c / ((j : ℝ) + 2))) *
        ∫ Z, nn (X c x0 T (j + 1) Z) ∂(iidLaw noiseLaw T) ≤
      ∫ Z, nn (X c x0 T (j + 1) Z) * X c x0 T (j + 1 + 1) Z ∂(iidLaw noiseLaw T) := by
  rw [← integral_const_mul]
  refine integral_mono_ae ((integ_nn c x0 T (j + 1)).const_mul _) (integ_nnX c x0 hx0 T _ _) ?_
  filter_upwards [ae_ext T] with Z hZ
  simp only [X]
  unfold nn
  split_ifs with h
  · have := neg_next_lower c x0 hc (extendNoise Z) hZ hx0 j ha h
    linarith
  · simp

/-- `E[n_k x_{k+1}] ≥ 0`. -/
lemma E3pos (c x0 : ℝ) (hc : 0 < c) (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (T k : ℕ) :
    0 ≤ ∫ Z, nn (X c x0 T k Z) * X c x0 T (k + 1) Z ∂(iidLaw noiseLaw T) := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_ext T] with Z hZ
  simp only [X, Pi.zero_apply]
  unfold nn
  split_ifs with h
  · have := (xs_sign c x0 hc (extendNoise Z) hZ hx0 k).2 h
    linarith
  · simp

/-- (E4) two steps after a negative iterate, using independence of `Z_{k+1}`. -/
lemma E4 (c x0 : ℝ) (hc : 0 < c) (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (T k : ℕ) (hk : k + 1 < T)
    (ha : 3 * (c / ((k : ℝ) + 2)) ≤ 1) :
    ∫ Z, nn (X c x0 T k Z) * X c x0 T (k + 2) Z ∂(iidLaw noiseLaw T) =
      (1 - c / ((k : ℝ) + 2)) * ∫ Z, nn (X c x0 T k Z) * X c x0 T (k + 1) Z ∂(iidLaw noiseLaw T)
        - c / ((k : ℝ) + 2) * ∫ Z, nn (X c x0 T k Z) ∂(iidLaw noiseLaw T) := by
  set a := c / ((k : ℝ) + 2) with ha_def
  have hE1 : Integrable (fun Z => (1 - a) * (nn (X c x0 T k Z) * X c x0 T (k + 1) Z))
      (iidLaw noiseLaw T) := (integ_nnX c x0 hx0 T k (k + 1)).const_mul _
  have hE2 : Integrable (fun Z : Fin T → ℝ => a * (nn (X c x0 T k Z) * Z ⟨k + 1, hk⟩))
      (iidLaw noiseLaw T) := (integ_nnZ c x0 T k (k + 1) hk).const_mul _
  have heq : ∀ᵐ Z ∂(iidLaw noiseLaw T), nn (X c x0 T k Z) * X c x0 T (k + 2) Z =
      (1 - a) * (nn (X c x0 T k Z) * X c x0 T (k + 1) Z) - a * (nn (X c x0 T k Z) * Z ⟨k + 1, hk⟩) := by
    filter_upwards [ae_ext T] with Z hZ
    simp only [X]
    unfold nn
    split_ifs with h
    · have := neg_next2 c x0 hc (extendNoise Z) hZ hx0 k ha h
      rw [this, extendNoise_lt Z (k + 1) hk]; ring
    · simp
  rw [integral_congr_ae heq, integral_sub hE1 hE2, integral_const_mul, integral_const_mul,
    int_nnZ c x0 T k (k + 1) (by omega) hk]

/-- (E5) the block inequalities in expectation. -/
lemma E5a (c x0 : ℝ) (hc : 0 < c) (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (T u : ℕ) :
    ∫ Z, nn (X c x0 T (u + 1) Z) * X c x0 T (u + 1) Z ∂(iidLaw noiseLaw T)
      + ∫ Z, nn (X c x0 T u Z) * X c x0 T (u + 1) Z ∂(iidLaw noiseLaw T)
      ≤ ∫ Z, X c x0 T (u + 1) Z ∂(iidLaw noiseLaw T) := by
  rw [← integral_add (integ_nnX c x0 hx0 T _ _) (integ_nnX c x0 hx0 T _ _)]
  refine integral_mono_ae ((integ_nnX c x0 hx0 T _ _).add (integ_nnX c x0 hx0 T _ _))
    (integ_X c x0 hx0 T _) ?_
  filter_upwards [ae_ext T] with Z hZ
  exact block1 c x0 hc (extendNoise Z) hZ hx0 u

lemma E5b (c x0 : ℝ) (hc : 0 < c) (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (T u : ℕ) :
    ∫ Z, nn (X c x0 T (u + 2) Z) * X c x0 T (u + 2) Z ∂(iidLaw noiseLaw T)
      + ∫ Z, nn (X c x0 T (u + 1) Z) * X c x0 T (u + 2) Z ∂(iidLaw noiseLaw T)
      + ∫ Z, nn (X c x0 T u Z) * X c x0 T (u + 2) Z ∂(iidLaw noiseLaw T)
      ≤ ∫ Z, X c x0 T (u + 2) Z ∂(iidLaw noiseLaw T) := by
  have hS : Integrable (fun Z => nn (X c x0 T (u + 2) Z) * X c x0 T (u + 2) Z
      + nn (X c x0 T (u + 1) Z) * X c x0 T (u + 2) Z) (iidLaw noiseLaw T) :=
    (integ_nnX c x0 hx0 T _ _).add (integ_nnX c x0 hx0 T _ _)
  rw [← integral_add (integ_nnX c x0 hx0 T _ _) (integ_nnX c x0 hx0 T _ _),
    ← integral_add hS (integ_nnX c x0 hx0 T _ _)]
  refine integral_mono_ae (hS.add (integ_nnX c x0 hx0 T _ _)) (integ_X c x0 hx0 T _) ?_
  filter_upwards [ae_ext T] with Z hZ
  exact block2 c x0 hc (extendNoise Z) hZ hx0 u

/-- Per-block ratio bound `l_k ≥ (3/8)(8 a_k + 3 a_k c/k)` (ALG ingredient). -/
lemma ratio_aux (c k : ℝ) (hc : 0 < c) (hk : 19 ≤ k) (hkc : 6 * c ≤ k) :
    (3 / 8) * (8 * (c / (k + 1)) + 3 * (c / (k + 1)) * (c / k)) ≤
      -(3 * c / k) + (2 - c / (k + 2)) *
        min 1 (7 * (c / (k + 1)) - 3 * (c / k) * (1 - c / (k + 1))) - c / (k + 2) := by
  have hk0 : 0 < k := by linarith
  set A := c / (k + 1) with hA
  set B := c / k with hB
  set C := c / (k + 2) with hC
  have hA0 : 0 < A := by positivity
  have hB0 : 0 < B := by positivity
  have hC0 : 0 < C := by positivity
  have hB6 : B ≤ 1 / 6 := by rw [hB, div_le_iff₀ hk0]; linarith
  have hAB : A ≤ B := div_le_div_of_nonneg_left hc.le hk0 (by linarith)
  have hCA : C ≤ A := div_le_div_of_nonneg_left hc.le (by linarith) (by linarith)
  -- B = A (k+1)/k ≤ A (20/19)
  have hBA : 19 * B ≤ 20 * A := by
    rw [hA, hB]
    rw [show 19 * (c / k) = 19 * c / k by ring, show 20 * (c / (k + 1)) = 20 * c / (k + 1) by ring,
      div_le_div_iff₀ hk0 (by linarith)]
    nlinarith
  have h3 : 3 * c / k = 3 * B := by rw [hB]; ring
  rw [h3]
  rcases le_total 1 (7 * A - 3 * B * (1 - A)) with hm | hm
  · rw [min_eq_left hm]
    nlinarith
  · rw [min_eq_right hm]
    nlinarith [mul_le_mul_of_nonneg_left hCA hA0.le, mul_pos hA0 hB0, mul_pos hC0 hA0,
      mul_pos (mul_pos hC0 hA0) hB0]

lemma blocks0 (q e r s : ℕ → ℝ) (h2' : ∀ k, e k ≤ q k)
    (h5a : ∀ u, e (u + 1) + r u ≤ q (u + 1))
    (h5b : ∀ u, e (u + 2) + r (u + 1) + s u ≤ q (u + 2)) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (e i + r i + s i) + e (n + 1) + r (n + 1) + e (n + 2)
      ≤ ∑ i ∈ Finset.range (n + 3), q i := by
  induction n with
  | zero =>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have h1 := h2' 0
    have h2 := h5a 0
    have h3 := h5b 0
    simp only [zero_add] at h2 h3
    linarith
  | succ n ih =>
    rw [Finset.sum_range_succ _ (n + 1), show n + 1 + 3 = (n + 3) + 1 from rfl,
      Finset.sum_range_succ _ (n + 3)]
    have h3 := h5b (n + 1)
    simp only [show n + 1 + 2 = n + 3 from rfl, show n + 1 + 1 = n + 2 from rfl] at h3 ⊢
    linarith

lemma alg (c : ℝ) (hc : 0 < c) (K L : ℕ) (hK : 19 ≤ (K : ℝ)) (hKc : 6 * c ≤ K)
    (q p e r s : ℕ → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (hE1 : ∀ k, K ≤ k → k ≤ K + L →
      q (k + 1) ≤ (1 - c / ((k : ℝ) + 1)) * q k - c / ((k : ℝ) + 1)
        + 8 * (c / ((k : ℝ) + 1)) * p k)
    (hE2 : ∀ k, K ≤ k → -(3 * c / (k : ℝ)) * p k ≤ e k)
    (hE2' : ∀ k, e k ≤ q k)
    (hE3 : ∀ k, K ≤ k → min 1 (7 * (c / ((k : ℝ) + 1)) - 3 * (c / (k : ℝ)) *
      (1 - c / ((k : ℝ) + 1))) * p k ≤ r k)
    (hE3pos : ∀ k, 0 ≤ r k)
    (hE4 : ∀ k, K ≤ k → k ≤ K + L →
      s k = (1 - c / ((k : ℝ) + 2)) * r k - c / ((k : ℝ) + 2) * p k)
    (hE5a : ∀ u, e (u + 1) + r u ≤ q (u + 1))
    (hE5b : ∀ u, e (u + 2) + r (u + 1) + s u ≤ q (u + 2))
    (hqK : q K ≤ 1) (hqlast : -(3 * c / ((K + L + 1 : ℕ) : ℝ)) ≤ q (K + L + 1)) :
    (3 / 8) * ∑ i ∈ Finset.range (L + 1), c / (((K + i : ℕ) : ℝ) + 1)
      - 3 / 8 - 8 * (c / ((K + L + 1 : ℕ) : ℝ)) ≤ ∑ i ∈ Finset.range (L + 3), q (K + i) := by
  obtain ⟨W, hW⟩ : ∃ W : ℕ → ℝ, W = fun k : ℕ => (8 * (c / ((k : ℝ) + 1))
      + 3 * (c / ((k : ℝ) + 1)) * (c / (k : ℝ))) * p k := ⟨_, rfl⟩
  have hw : ∀ k, K ≤ k → k ≤ K + L → c / ((k : ℝ) + 1) ≤ q k - q (k + 1) + W k := by
    intro k hk1 hk2
    have hkR : (K : ℝ) ≤ k := by exact_mod_cast hk1
    have hk0 : (0 : ℝ) < k := by linarith
    have h1 := hE1 k hk1 hk2
    have h2 := hE2 k hk1
    have h3 := hE2' k
    have ha : 0 ≤ c / ((k : ℝ) + 1) := by positivity
    rw [show 3 * c / (k : ℝ) = 3 * (c / k) by ring] at h2
    have h4 := mul_le_mul_of_nonneg_left h3 ha
    have h5 := mul_le_mul_of_nonneg_left h2 ha
    rw [hW]
    simp only
    nlinarith
  have hb : ∀ k, K ≤ k → k ≤ K + L → (3 / 8) * W k ≤ e k + r k + s k := by
    intro k hk1 hk2
    have hkR : (K : ℝ) ≤ k := by exact_mod_cast hk1
    have hk0 : (0 : ℝ) < k := by linarith
    have hrat := ratio_aux c k hc (by linarith) (by linarith)
    have h2 := hE2 k hk1
    have h3 := hE3 k hk1
    have h4 := hE4 k hk1 hk2
    have hC : c / ((k : ℝ) + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have h5 := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ 2 - c / ((k : ℝ) + 2) by linarith)
    have h6 := mul_le_mul_of_nonneg_right hrat (hp0 k)
    rw [h4, hW]
    simp only
    nlinarith
  have hD : 0 < c / ((K + L + 1 : ℕ) : ℝ) := by positivity
  -- telescoped drift
  have hsum1 : ∑ i ∈ Finset.range (L + 1), c / (((K + i : ℕ) : ℝ) + 1) ≤
      (q K - q (K + L + 1)) + ∑ i ∈ Finset.range (L + 1), W (K + i) := by
    have h := Finset.sum_le_sum (fun i (hi : i ∈ Finset.range (L + 1)) =>
      hw (K + i) (by omega) (by simp at hi; omega))
    have htel : ∑ x ∈ Finset.range (L + 1), (q (K + x) - q (K + x + 1)) = q K - q (K + L + 1) := by
      have := Finset.sum_range_sub' (fun i => q (K + i)) (L + 1)
      simp only [add_assoc, add_zero] at this ⊢
      exact this
    rw [Finset.sum_add_distrib, htel] at h
    exact h
  have hsum2 : (3 / 8) * ∑ i ∈ Finset.range (L + 1), W (K + i) ≤
      ∑ i ∈ Finset.range (L + 1), (e (K + i) + r (K + i) + s (K + i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => hb (K + i) (by omega) (by simp at hi; omega))
  have hblk := blocks0 (fun i => q (K + i)) (fun i => e (K + i)) (fun i => r (K + i))
    (fun i => s (K + i)) (fun k => hE2' (K + k)) (fun u => hE5a (K + u)) (fun u => hE5b (K + u)) L
  try simp only at hblk
  have hb1 := hE2 (K + (L + 1)) (by omega)
  have hb2 := hE2 (K + (L + 2)) (by omega)
  have hb3 := hE3pos (K + (L + 1))
  have hp1' := hp1 (K + (L + 1))
  have hp2' := hp1 (K + (L + 2))
  have hp1'' := hp0 (K + (L + 1))
  have hp2'' := hp0 (K + (L + 2))
  have hd1 : 3 * c / (((K + (L + 1) : ℕ) : ℝ)) = 3 * (c / ((K + L + 1 : ℕ) : ℝ)) := by
    rw [show K + (L + 1) = K + L + 1 by omega]; ring
  have hd2 : 3 * c / (((K + (L + 2) : ℕ) : ℝ)) ≤ 3 * (c / ((K + L + 1 : ℕ) : ℝ)) := by
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hc.le (by positivity) ?_) (by norm_num)
    exact_mod_cast (show K + L + 1 ≤ K + (L + 2) by omega)
  have hd3 : 3 * c / ((K + L + 1 : ℕ) : ℝ) = 3 * (c / ((K + L + 1 : ℕ) : ℝ)) := by ring
  rw [hd1] at hb1
  rw [hd3] at hqlast
  have hx2 : -(3 * (c / ((K + L + 1 : ℕ) : ℝ))) ≤ -(3 * c / (((K + (L + 2) : ℕ) : ℝ))) * p (K + (L + 2)) := by
    nlinarith [div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hc.le)
      (Nat.cast_nonneg (α := ℝ) (K + (L + 2)))]
  have hx1 : -(3 * (c / ((K + L + 1 : ℕ) : ℝ))) ≤ -(3 * (c / ((K + L + 1 : ℕ) : ℝ))) * p (K + (L + 1)) := by
    nlinarith
  rw [show K + (L + 1) = K + L + 1 by omega] at hb1 hb3 hx1
  rw [show K + (L + 2) = K + L + 2 by omega] at hb2 hx2
  rw [show K + (L + 1) = K + L + 1 by omega, show K + (L + 2) = K + L + 2 by omega] at hblk
  linarith

lemma sum_split (f : ℕ → ℝ) (M K L : ℕ) (hM : M ≤ K + 1) :
    ∑ t ∈ Finset.Icc M (K + L + 3), f t = ∑ t ∈ Finset.Icc M K, f t
      + ∑ i ∈ Finset.range (L + 1), f (K + i + 1) + f (K + L + 2) + f (K + L + 3) := by
  induction L with
  | zero =>
    rw [show K + 0 + 3 = (K + 2) + 1 from rfl, Finset.sum_Icc_succ_top (by omega),
      show K + 2 = (K + 1) + 1 from rfl, Finset.sum_Icc_succ_top (by omega),
      Finset.sum_Icc_succ_top hM]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring_nf
  | succ L ih =>
    rw [show K + (L + 1) + 3 = (K + L + 3) + 1 by omega, Finset.sum_Icc_succ_top (by omega), ih,
      Finset.sum_range_succ _ (L + 1)]
    ring_nf

lemma H18 : ∑ j ∈ Finset.range 18, (1 : ℝ) / ((j : ℝ) + 1) ≤ 7 / 2 := by
  norm_num [Finset.sum_range_succ]

lemma H4_19 : ∑ t ∈ Finset.Icc (4 : ℕ) 19, (1 : ℝ) / ((t : ℕ) : ℝ) ≤ 172 / 100 := by
  rw [show Finset.Icc (4 : ℕ) 19 = {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19} by decide]
  norm_num

lemma tail_le (c : ℝ) (hc : 0 < c) (m n : ℕ) (h : n ≤ m) (hn : 0 < n) :
    c * ((1 : ℝ) / (m : ℝ)) ≤ c / (n : ℝ) := by
  rw [mul_one_div]
  exact div_le_div_of_nonneg_left hc.le (by exact_mod_cast hn) (by exact_mod_cast h)

lemma final_real (c : ℝ) (hc : 0 < c) (T : ℕ) (q : ℕ → ℝ)
    (hT : max 2 (6 * c + 1) + 2 ≤ (T : ℝ))
    (hq1 : ∀ k, -1 ≤ q k) (hq0 : 0 ≤ q 0) (hqs : ∀ j : ℕ, -(3 * c / ((j : ℝ) + 1)) ≤ q (j + 1))
    (halg : ∀ K L : ℕ, 19 ≤ (K : ℝ) → 6 * c ≤ K → K + L + 3 = T →
      (3 / 8) * ∑ i ∈ Finset.range (L + 1), c / (((K + i : ℕ) : ℝ) + 1) - 3 / 8
        - 8 * (c / ((K + L + 1 : ℕ) : ℝ)) ≤ ∑ i ∈ Finset.range (L + 3), q (K + i))
    (hnt : max 2 (6 * c + 1) < 3 * c / 16 *
      ∑ t ∈ Finset.Icc (⌈max 2 (6 * c + 1)⌉₊ + 2) T, (1 : ℝ) / (t : ℝ)) :
    3 * c / 16 * ∑ t ∈ Finset.Icc (⌈max 2 (6 * c + 1)⌉₊ + 2) T, (1 : ℝ) / (t : ℝ)
      - max 2 (6 * c + 1) ≤ ∑ k ∈ Finset.range T, q k := by
  set T0 := max 2 (6 * c + 1) with hT0
  set N := ⌈T0⌉₊ with hN
  set S := ∑ t ∈ Finset.Icc (N + 2) T, (1 : ℝ) / (t : ℝ) with hS
  have hT02 : 2 ≤ T0 := le_max_left _ _
  have hT0c : 6 * c + 1 ≤ T0 := le_max_right _ _
  have hN1 : T0 ≤ N := Nat.le_ceil _
  have hN2 : (N : ℝ) < T0 + 1 := Nat.ceil_lt_add_one (by linarith)
  have hNT : N + 2 ≤ T := by
    have : ((N + 2 : ℕ) : ℝ) < ((T + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := (Nat.cast_lt (α := ℝ)).mp this
    omega
  have hN2' : 2 ≤ N := by
    have : (2 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hterm : ∀ t ∈ Finset.Icc (N + 2) T, (1 : ℝ) / (t : ℝ) ≤ 1 / ((N : ℝ) + 2) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    have : ((N : ℝ) + 2) ≤ t := by exact_mod_cast ht.1
    exact one_div_le_one_div_of_le (by positivity) this
  have hSle : S ≤ ((T + 1 - (N + 2) : ℕ) : ℝ) * (1 / ((N : ℝ) + 2)) := by
    have := Finset.sum_le_card_nsmul _ _ _ hterm
    rw [Nat.card_Icc, nsmul_eq_mul] at this
    exact this
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun t _ => by positivity)
  by_cases hcase : 18 ≤ N
  · have hNR : (18 : ℝ) ≤ N := by exact_mod_cast hcase
    by_cases hTs : T ≤ N + 3
    · exfalso
      have hcard : ((T + 1 - (N + 2) : ℕ) : ℝ) ≤ 2 := by
        exact_mod_cast (show T + 1 - (N + 2) ≤ 2 by omega)
      have h1 : S ≤ 2 * (1 / ((N : ℝ) + 2)) :=
        le_trans hSle (mul_le_mul_of_nonneg_right hcard (by positivity))
      have h2 : 3 * c / 16 * S ≤ 3 * c / 16 * (2 * (1 / ((N : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : 3 * c / 16 * (2 * (1 / ((N : ℝ) + 2))) ≤ 1 := by
        rw [show 3 * c / 16 * (2 * (1 / ((N : ℝ) + 2))) = (3 * c) / (8 * ((N : ℝ) + 2)) by
          field_simp; ring]
        rw [div_le_one (by positivity)]
        linarith
      linarith
    · push Not at hTs
      obtain ⟨L, hL⟩ : ∃ L, T = (N + 1) + L + 3 := ⟨T - N - 4, by omega⟩
      have h := halg (N + 1) L (by push_cast; linarith) (by push_cast; linarith) hL.symm
      have hsplit := sum_split (fun t : ℕ => (1 : ℝ) / (t : ℝ)) (N + 2) (N + 1) L (by omega)
      rw [← hL, Finset.Icc_eq_empty (show ¬ (N + 2 ≤ N + 1) by omega), Finset.sum_empty, zero_add] at hsplit
      have hsum : ∑ i ∈ Finset.range (L + 1), c / (((N + 1 + i : ℕ) : ℝ) + 1) =
          c * ∑ i ∈ Finset.range (L + 1), (1 : ℝ) / (((N + 1 + i + 1 : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        push_cast
        ring
      have ht1 := tail_le c hc (N + 1 + L + 2) (N + 1 + L + 1) (by omega) (by omega)
      have ht2 := tail_le c hc (N + 1 + L + 3) (N + 1 + L + 1) (by omega) (by omega)
      have hε : c / ((N + 1 + L + 1 : ℕ) : ℝ) ≤ 1 / 6 := by
        rw [div_le_iff₀ (by positivity)]
        push_cast
        linarith
      have hε0 : 0 ≤ c / ((N + 1 + L + 1 : ℕ) : ℝ) := by positivity
      have hearly : -((N : ℝ) + 1) ≤ ∑ k ∈ Finset.range (N + 1), q k := by
        have := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range (N + 1)) => hq1 k)
        simpa using this
      have hQ : ∑ k ∈ Finset.range T, q k = ∑ k ∈ Finset.range (N + 1), q k
          + ∑ i ∈ Finset.range (L + 3), q (N + 1 + i) := by
        rw [hL, show N + 1 + L + 3 = (N + 1) + (L + 3) by omega, Finset.sum_range_add]
      try simp only at hsplit
      have hcS : c * S = c * ∑ i ∈ Finset.range (L + 1), (1 : ℝ) / (((N + 1 + i + 1 : ℕ) : ℝ))
          + c * ((1 : ℝ) / (((N + 1 + L + 2 : ℕ) : ℝ))) + c * ((1 : ℝ) / (((N + 1 + L + 3 : ℕ) : ℝ))) := by
        rw [hS, hsplit, hL]; push_cast; ring
      rw [hsum] at h
      rw [hQ]
      nlinarith
  · push Not at hcase
    have hc16 : 6 * c ≤ 16 := by
      have : (N : ℝ) ≤ 17 := by exact_mod_cast (show N ≤ 17 by omega)
      linarith
    by_cases hTs : T ≤ 21
    · exfalso
      have hcard : ((T + 1 - (N + 2) : ℕ) : ℝ) ≤ 18 := by
        exact_mod_cast (show T + 1 - (N + 2) ≤ 18 by omega)
      have hN4 : (4 : ℝ) ≤ (N : ℝ) + 2 := by
        have : (2 : ℝ) ≤ N := by exact_mod_cast hN2'
        linarith
      have h1 : S ≤ 18 * (1 / 4) := le_trans hSle (mul_le_mul hcard
        (one_div_le_one_div_of_le (by norm_num) hN4) (by positivity) (by norm_num))
      have h2 : 3 * c / 16 * S ≤ 3 * c / 16 * (18 * (1 / 4)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      nlinarith
    · push Not at hTs
      obtain ⟨L, hL⟩ : ∃ L, T = 19 + L + 3 := ⟨T - 22, by omega⟩
      have h := halg 19 L (by norm_num) (by push_cast; linarith) hL.symm
      have hsplit := sum_split (fun t : ℕ => (1 : ℝ) / (t : ℝ)) (N + 2) 19 L (by omega)
      rw [← hL] at hsplit
      have hM : ∑ t ∈ Finset.Icc (N + 2) 19, (1 : ℝ) / (t : ℝ) ≤ 172 / 100 :=
        le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (show 4 ≤ N + 2 by omega) le_rfl)
          (fun t _ _ => by positivity)) H4_19
      have hM0 : 0 ≤ ∑ t ∈ Finset.Icc (N + 2) 19, (1 : ℝ) / (t : ℝ) :=
        Finset.sum_nonneg (fun t _ => by positivity)
      have hsum : ∑ i ∈ Finset.range (L + 1), c / (((19 + i : ℕ) : ℝ) + 1) =
          c * ∑ i ∈ Finset.range (L + 1), (1 : ℝ) / (((19 + i + 1 : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        push_cast
        ring
      have ht1 := tail_le c hc (19 + L + 2) (19 + L + 1) (by omega) (by omega)
      have ht2 := tail_le c hc (19 + L + 3) (19 + L + 1) (by omega) (by omega)
      have hε : c / ((19 + L + 1 : ℕ) : ℝ) ≤ c / 20 :=
        div_le_div_of_nonneg_left hc.le (by norm_num) (by push_cast; linarith [(Nat.cast_nonneg L : (0:ℝ) ≤ L)])
      have hearly : -(3 * c * (7 / 2)) ≤ ∑ k ∈ Finset.range 19, q k := by
        rw [Finset.sum_range_succ']
        have h1 := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range 18) => hqs j)
        have h2 : ∑ j ∈ Finset.range 18, -(3 * c / ((j : ℝ) + 1)) =
            -(3 * c) * ∑ j ∈ Finset.range 18, (1 : ℝ) / ((j : ℝ) + 1) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          ring
        rw [h2] at h1
        nlinarith [H18]
      have hQ : ∑ k ∈ Finset.range T, q k = ∑ k ∈ Finset.range 19, q k
          + ∑ i ∈ Finset.range (L + 3), q (19 + i) := by
        rw [hL, show 19 + L + 3 = 19 + (L + 3) by omega, Finset.sum_range_add]
      try simp only at hsplit
      have hcS : c * S = c * ∑ t ∈ Finset.Icc (N + 2) 19, (1 : ℝ) / (t : ℝ)
          + c * ∑ i ∈ Finset.range (L + 1), (1 : ℝ) / (((19 + i + 1 : ℕ) : ℝ))
          + c * ((1 : ℝ) / (((19 + L + 2 : ℕ) : ℝ))) + c * ((1 : ℝ) / (((19 + L + 3 : ℕ) : ℝ))) := by
        rw [hS, hsplit, hL]; push_cast; ring
      have hcM := mul_le_mul_of_nonneg_left hM hc.le
      rw [hsum] at h
      rw [hQ]
      nlinarith


lemma int_ge {T : ℕ} {f : (Fin T → ℝ) → ℝ} (hf : Integrable f (iidLaw noiseLaw T)) (b : ℝ)
    (h : ∀ᵐ Z ∂(iidLaw noiseLaw T), b ≤ f Z) : b ≤ ∫ Z, f Z ∂(iidLaw noiseLaw T) := by
  have := integral_mono_ae (integrable_const b) hf h
  simpa using this

lemma int_le {T : ℕ} {f : (Fin T → ℝ) → ℝ} (hf : Integrable f (iidLaw noiseLaw T)) (b : ℝ)
    (h : ∀ Z, f Z ≤ b) : ∫ Z, f Z ∂(iidLaw noiseLaw T) ≤ b := by
  have := integral_mono hf (integrable_const b) h
  simpa using this

lemma avg_abs {d : ℕ} [NeZero d] (c : ℝ) (w₁ : Vec d) (hw₁ : w₁ ∈ box (-1) 1) {T : ℕ}
    (Z : Fin T → ℝ) (i : Fin d) : |(avgB c w₁ Z) i| ≤ 1 := by
  rw [avgB_apply, abs_mul]
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT; simp
  · have h1 : |∑ t ∈ Finset.range T, (runB c w₁ (extendNoise Z) t) i| ≤ T := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have := Finset.sum_le_card_nsmul (Finset.range T)
        (fun t => |(runB c w₁ (extendNoise Z) t) i|) 1 (fun t _ =>
          abs_le.2 ⟨(runB_mem c w₁ hw₁ _ t i).1, (runB_mem c w₁ hw₁ _ t i).2⟩)
      simpa using this
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (T : ℝ)⁻¹)]
    calc (T : ℝ)⁻¹ * |∑ t ∈ Finset.range T, (runB c w₁ (extendNoise Z) t) i|
        ≤ (T : ℝ)⁻¹ * T := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := inv_mul_cancel₀ hTpos.ne'

lemma objB_le {d : ℕ} [NeZero d] (w : Vec d) (h : ∀ i, |w i| ≤ 1) :
    objB w ≤ (d : ℝ) / 2 + 7 := by
  have hn : ‖w‖ ^ 2 ≤ d := by
    rw [EuclideanSpace.norm_sq_eq]
    have := Finset.sum_le_card_nsmul Finset.univ (fun i => ‖w i‖ ^ 2) 1 (fun i _ => by
      rw [Real.norm_eq_abs, sq_abs]
      nlinarith [h i, abs_nonneg (w i), sq_abs (w i)])
    simpa using this
  have h0 := abs_le.1 (h 0)
  unfold objB
  split_ifs <;> nlinarith [h0.1, h0.2]

theorem main_thm (d : ℕ) [NeZero d] (c : ℝ) (hc : 0 < c) (w₁ : Vec d)
    (hw₁ : w₁ ∈ box (-1) 1) (hw₁₁ : 0 ≤ w₁ 0) (T : ℕ)
    (hT : max 2 (6 * c + 1) + 2 ≤ (T : ℝ)) :
    Integrable (fun Z : Fin T → ℝ => objB (avgB c w₁ Z) - objB (0 : Vec d))
        (iidLaw noiseLaw T) ∧
      3 * c / (16 * (T : ℝ)) *
          (∑ t ∈ Finset.Icc (⌈max 2 (6 * c + 1)⌉₊ + 2) T, (1 : ℝ) / (t : ℝ))
          - max 2 (6 * c + 1) / (T : ℝ)
        ≤ ∫ Z, (objB (avgB c w₁ Z) - objB (0 : Vec d)) ∂(iidLaw noiseLaw T) := by
  have hx0 : w₁ 0 ∈ Set.Icc (0 : ℝ) 1 := ⟨hw₁₁, (hw₁ 0).2⟩
  have hTpos : (0 : ℝ) < T := by linarith [le_max_left (2 : ℝ) (6 * c + 1)]
  have hmeas : Measurable (fun Z : Fin T → ℝ => objB (avgB c w₁ Z) - objB (0 : Vec d)) :=
    (measurable_objB_avgB c w₁ T).sub measurable_const
  have hint : Integrable (fun Z : Fin T → ℝ => objB (avgB c w₁ Z) - objB (0 : Vec d))
      (iidLaw noiseLaw T) := by
    refine integ_bdd hmeas ((d : ℝ) / 2 + 7) (Filter.Eventually.of_forall (fun Z => ?_))
    rw [objB_zero', sub_zero, abs_of_nonneg (objB_ge _).2]
    exact objB_le _ (fun i => avg_abs c w₁ hw₁ Z i)
  refine ⟨hint, ?_⟩
  set x0 := w₁ 0 with hx0def
  have hlow : ∀ Z : Fin T → ℝ, (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, X c x0 T k Z ≤
      objB (avgB c w₁ Z) - objB (0 : Vec d) := by
    intro Z
    rw [objB_zero', sub_zero]
    have h := (objB_ge (avgB c w₁ Z)).1
    rw [avgB_apply] at h
    simp only [runB_zero] at h
    exact h
  have hQ : (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, ∫ Z, X c x0 T k Z ∂(iidLaw noiseLaw T) ≤
      ∫ Z, (objB (avgB c w₁ Z) - objB (0 : Vec d)) ∂(iidLaw noiseLaw T) := by
    rw [← integral_finsetSum _ (fun k _ => integ_X c x0 hx0 T k), ← integral_const_mul]
    exact integral_mono ((integrable_finsetSum _ (fun k _ => integ_X c x0 hx0 T k)).const_mul _)
      hint hlow
  have hnn : 0 ≤ ∫ Z, (objB (avgB c w₁ Z) - objB (0 : Vec d)) ∂(iidLaw noiseLaw T) :=
    integral_nonneg (fun Z => by rw [objB_zero', sub_zero]; exact (objB_ge _).2)
  have hq1 : ∀ k, -1 ≤ ∫ Z, X c x0 T k Z ∂(iidLaw noiseLaw T) := fun k =>
    int_ge (integ_X c x0 hx0 T k) _ (Filter.Eventually.of_forall (fun Z =>
      (abs_le.1 (abs_X_le c x0 hx0 T k Z)).1))
  have hq0 : 0 ≤ ∫ Z, X c x0 T 0 Z ∂(iidLaw noiseLaw T) :=
    int_ge (integ_X c x0 hx0 T 0) _ (Filter.Eventually.of_forall (fun Z => hx0.1))
  have hqs : ∀ j : ℕ, -(3 * c / ((j : ℝ) + 1)) ≤ ∫ Z, X c x0 T (j + 1) Z ∂(iidLaw noiseLaw T) :=
    fun j => int_ge (integ_X c x0 hx0 T (j + 1)) _ (by
      filter_upwards [ae_ext T] with Z hZ
      exact (xs_sign c x0 hc (extendNoise Z) hZ hx0 j).1)
  have halg : ∀ K L : ℕ, 19 ≤ (K : ℝ) → 6 * c ≤ K → K + L + 3 = T →
      (3 / 8) * ∑ i ∈ Finset.range (L + 1), c / (((K + i : ℕ) : ℝ) + 1) - 3 / 8
        - 8 * (c / ((K + L + 1 : ℕ) : ℝ)) ≤
        ∑ i ∈ Finset.range (L + 3), ∫ Z, X c x0 T (K + i) Z ∂(iidLaw noiseLaw T) := by
    intro K L hK hKc hKT
    have hK19 : 19 ≤ K := by exact_mod_cast hK
    refine alg c hc K L hK hKc (fun k => ∫ Z, X c x0 T k Z ∂(iidLaw noiseLaw T))
      (fun k => ∫ Z, nn (X c x0 T k Z) ∂(iidLaw noiseLaw T))
      (fun k => ∫ Z, nn (X c x0 T k Z) * X c x0 T k Z ∂(iidLaw noiseLaw T))
      (fun k => ∫ Z, nn (X c x0 T k Z) * X c x0 T (k + 1) Z ∂(iidLaw noiseLaw T))
      (fun k => ∫ Z, nn (X c x0 T k Z) * X c x0 T (k + 2) Z ∂(iidLaw noiseLaw T))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro k
      exact integral_nonneg (fun Z => nn_nonneg _)
    · intro k
      exact int_le (integ_nn c x0 T k) 1 (fun Z => nn_le_one _)
    · intro k hk1 hk2
      have hkR : (K : ℝ) ≤ k := by exact_mod_cast hk1
      exact E1 c x0 hc hx0 T k (by omega)
        (by rw [← mul_div_assoc, div_le_one (by positivity)]; linarith)
    · intro k hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have h := E2 c x0 hc hx0 T j
      push_cast
      exact h
    · intro k
      exact E2' c x0 hx0 T k
    · intro k hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hkR : (K : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast hk
      have h := E3 c x0 hc hx0 T j (by rw [div_le_one (by positivity)]; linarith)
      rw [show ((j + 1 : ℕ) : ℝ) + 1 = (j : ℝ) + 2 by push_cast; ring,
        show ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 by push_cast; ring]
      exact h
    · intro k
      exact E3pos c x0 hc hx0 T k
    · intro k hk1 hk2
      have hkR : (K : ℝ) ≤ k := by exact_mod_cast hk1
      exact E4 c x0 hc hx0 T k (by omega)
        (by rw [← mul_div_assoc, div_le_one (by positivity)]; linarith)
    · intro u
      exact E5a c x0 hc hx0 T u
    · intro u
      exact E5b c x0 hc hx0 T u
    · exact int_le (integ_X c x0 hx0 T K) 1 (fun Z => (abs_le.1 (abs_X_le c x0 hx0 T K Z)).2)
    · have e : ((K + L + 1 : ℕ) : ℝ) = ((K + L : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [e]
      exact hqs (K + L)
  have htgt : 3 * c / (16 * (T : ℝ)) *
        (∑ t ∈ Finset.Icc (⌈max 2 (6 * c + 1)⌉₊ + 2) T, (1 : ℝ) / (t : ℝ))
        - max 2 (6 * c + 1) / (T : ℝ) =
      (3 * c / 16 * (∑ t ∈ Finset.Icc (⌈max 2 (6 * c + 1)⌉₊ + 2) T, (1 : ℝ) / (t : ℝ))
        - max 2 (6 * c + 1)) / (T : ℝ) := by
    field_simp
  rw [htgt]
  by_cases hnt : max 2 (6 * c + 1) < 3 * c / 16 *
      ∑ t ∈ Finset.Icc (⌈max 2 (6 * c + 1)⌉₊ + 2) T, (1 : ℝ) / (t : ℝ)
  · have key := final_real c hc T (fun k => ∫ Z, X c x0 T k Z ∂(iidLaw noiseLaw T)) hT hq1 hq0
      hqs halg hnt
    calc _ ≤ (∑ k ∈ Finset.range T, ∫ Z, X c x0 T k Z ∂(iidLaw noiseLaw T)) / (T : ℝ) :=
          div_le_div_of_nonneg_right key hTpos.le
      _ = (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, ∫ Z, X c x0 T k Z ∂(iidLaw noiseLaw T) := by ring
      _ ≤ _ := hQ
  · push Not at hnt
    have : (3 * c / 16 * (∑ t ∈ Finset.Icc (⌈max 2 (6 * c + 1)⌉₊ + 2) T, (1 : ℝ) / (t : ℝ))
        - max 2 (6 * c + 1)) / (T : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hTpos.le
    linarith

end SGDB4

open MeasureTheory UnderstandingML OptimalSGD.LowerBound in
theorem solution (d : ℕ) [NeZero d] (c : ℝ) (hc : 0 < c) (w₁ : Vec d)
    (hw₁ : w₁ ∈ box (-1) 1) (hw₁₁ : 0 ≤ w₁ 0) (T : ℕ)
    (hT : max 2 (6 * c + 1) + 2 ≤ (T : ℝ)) :
    Integrable (fun Z : Fin T → ℝ => objB (avgB c w₁ Z) - objB (0 : Vec d))
        (iidLaw noiseLaw T) ∧
      3 * c / (16 * (T : ℝ)) *
          (∑ t ∈ Finset.Icc (⌈max 2 (6 * c + 1)⌉₊ + 2) T, (1 : ℝ) / (t : ℝ))
          - max 2 (6 * c + 1) / (T : ℝ)
        ≤ ∫ Z, (objB (avgB c w₁ Z) - objB (0 : Vec d)) ∂(iidLaw noiseLaw T) := by
  exact SGDB4.main_thm d c hc w₁ hw₁ hw₁₁ T hT
