-- Prove2me | solution 1 for RandomListsMatching.Concentration.lemma1_alg_lower_tail
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:26:48.469045+00:00
-- url     : https://prove2.me/submissions/4b91da9a-ce54-4679-aefd-8e8cbaffdca2

import Mathlib
import Definitions.Def_RandomListsMatching_Concentration_Setting

open scoped BigOperators
open MeasureTheory RandomListsMatching.Concentration

noncomputable section

private lemma exp_two_mul_sub_le (x : ℝ) (hx : 0 ≤ x) :
    (1 - x) * Real.exp (2 * x) ≤ 1 + x := by
  let f : ℝ → ℝ := fun u => 1 + u - (1 - u) * Real.exp (2 * u)
  have hderiv : ∀ u : ℝ, HasDerivAt f (1 - (1 - 2 * u) * Real.exp (2 * u)) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => 1 + u) 1 u :=
      (hasDerivAt_id u).const_add (1 : ℝ)
    have h2 : HasDerivAt (fun u : ℝ => 1 - u) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub (1 : ℝ)
    have h3 : HasDerivAt (fun u : ℝ => Real.exp (2 * u)) (Real.exp (2 * u) * 2) u := by
      have hexp : HasDerivAt Real.exp (Real.exp (2 * u)) (2 * u) := Real.hasDerivAt_exp (2 * u)
      have hlin : HasDerivAt (fun u : ℝ => 2 * u) 2 u := by
        simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
      exact HasDerivAt.comp u hexp hlin
    exact (h1.sub (h2.mul h3)).congr_deriv (by ring)
  have hdiff : Differentiable ℝ f := fun u => (hderiv u).differentiableAt
  have hderiv_nonneg : ∀ u : ℝ, 0 ≤ deriv f u := by
    intro u
    rw [(hderiv u).deriv]
    have hle : -2 * u + 1 ≤ Real.exp (-2 * u) := Real.add_one_le_exp (-2 * u)
    have hmul : (1 - 2 * u) * Real.exp (2 * u) ≤ Real.exp (-2 * u) * Real.exp (2 * u) := by
      have : 1 - 2 * u ≤ Real.exp (-2 * u) := by linarith
      exact mul_le_mul_of_nonneg_right this (Real.exp_nonneg (2 * u))
    rw [← Real.exp_add] at hmul
    have h0 : (-2 * u) + 2 * u = 0 := by ring
    rw [h0, Real.exp_zero] at hmul
    linarith
  have hmono : Monotone f := monotone_of_deriv_nonneg hdiff hderiv_nonneg
  have h0 : f 0 ≤ f x := hmono hx
  dsimp [f] at h0
  rw [ mul_zero, Real.exp_zero] at h0
  linarith

private lemma exp_sub_one_mul_sq_le (t : ℝ) (ht0 : 0 ≤ t) (ht4 : t ≤ 4) :
    (Real.exp t - 1) * (1 - t / 4) ^ 2 ≤ t := by
  let x : ℝ := t / 4
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hx1 : x ≤ 1 := by dsimp [x]; linarith
  have h1 : (1 - x) * Real.exp (2 * x) ≤ 1 + x := exp_two_mul_sub_le x hx0
  have hnonneg : 0 ≤ (1 - x) * Real.exp (2 * x) :=
    mul_nonneg (by linarith) (Real.exp_nonneg (2 * x))
  have hsq : ((1 - x) * Real.exp (2 * x)) ^ 2 ≤ (1 + x) ^ 2 :=
     sq_le_sq.mpr (by rw [abs_of_nonneg hnonneg, abs_of_nonneg (by linarith)]; exact h1)
  have hexp : (Real.exp (2 * x)) ^ 2 = Real.exp t := by
    rw [sq, ← Real.exp_add]
    congr 1
    dsimp [x]
    ring
  have h2 : (1 - x) ^ 2 * Real.exp t ≤ (1 + x) ^ 2 := by
    calc
      (1 - x) ^ 2 * Real.exp t = (1 - x) ^ 2 * (Real.exp (2 * x)) ^ 2 := by rw [hexp]
      _ = ((1 - x) * Real.exp (2 * x)) ^ 2 := by ring
      _ ≤ (1 + x) ^ 2 := hsq
  have hid : (Real.exp t - 1) * (1 - x) ^ 2 =
      (1 - x) ^ 2 * Real.exp t - (1 + x) ^ 2 + 4 * x := by ring
  have h4x : 4 * x = t := by dsimp [x]; ring
  change (Real.exp t - 1) * (1 - x) ^ 2 ≤ t
  linarith

private lemma hoeffding_deriv_factor_nonpos (p t : ℝ) (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) (ht0 : 0 ≤ t) :
    p * Real.exp t + (1 - p + p * Real.exp t) * (-p - t / 4) ≤ 0 := by
  let D : ℝ := Real.exp t - 1
  have hD : 0 ≤ D := sub_nonneg.mpr (Real.one_le_exp ht0)
  by_cases ht4 : t ≤ 4
  · have hid : p * Real.exp t + (1 - p + p * Real.exp t) * (-p - t / 4) =
        -D * (p - (1 - t / 4) / 2) ^ 2 + (D * (1 - t / 4) ^ 2 - t) / 4 := by
      dsimp [D]
      ring
    rw [hid]
    have h1 : 0 ≤ D * (p - (1 - t / 4) / 2) ^ 2 := mul_nonneg hD (sq_nonneg _)
    have h2 : D * (1 - t / 4) ^ 2 ≤ t := exp_sub_one_mul_sq_le t ht0 ht4
    linarith
  · have hid : p * Real.exp t + (1 - p + p * Real.exp t) * (-p - t / 4) =
        -D * p ^ 2 - D * (t / 4 - 1) * p - t / 4 := by
      dsimp [D]
      ring
    rw [hid]
    have h1 : 0 ≤ D * p ^ 2 := mul_nonneg hD (sq_nonneg p)
    have h2 : 0 ≤ D * (t / 4 - 1) * p :=
      mul_nonneg (mul_nonneg hD (by linarith)) hp0
    linarith

private lemma hoeffding_bernoulli_bound (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht0 : 0 ≤ t) :
    (1 - p + p * Real.exp t) * Real.exp (-p * t) ≤ Real.exp (t ^ 2 / 8) := by
  let Φ : ℝ → ℝ := fun u => (1 - p + p * Real.exp u) * Real.exp (-p * u - u ^ 2 / 8)
  have hderiv : ∀ u : ℝ, HasDerivAt Φ
      ((p * Real.exp u + (1 - p + p * Real.exp u) * (-p - u / 4)) *
        Real.exp (-p * u - u ^ 2 / 8)) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => 1 - p + p * Real.exp u) (p * Real.exp u) u :=
      ((Real.hasDerivAt_exp u).const_mul p).const_add (1 - p)
    have h2_inner : HasDerivAt (fun u : ℝ => -p * u - u ^ 2 / 8) (-p - u / 4) u := by
      have ha : HasDerivAt (fun u : ℝ => -p * u) (-p) u := by
        simpa using (hasDerivAt_id u).const_mul (-p)
      have hb : HasDerivAt (fun u : ℝ => u ^ 2 / 8) (2 * u / 8) u := by
        simpa using (hasDerivAt_pow 2 u).div_const 8
      exact (ha.sub hb).congr_deriv (by ring)
    have h2 : HasDerivAt (fun u : ℝ => Real.exp (-p * u - u ^ 2 / 8))
        (Real.exp (-p * u - u ^ 2 / 8) * (-p - u / 4)) u :=
      h2_inner.exp
    exact (h1.mul h2).congr_deriv (by ring)
  have hcont : ContinuousOn Φ (Set.Ici 0) :=
    fun u _ => (hderiv u).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ Φ (interior (Set.Ici 0)) :=
    fun u _ => (hderiv u).differentiableAt.differentiableWithinAt
  have hderiv_nonpos : ∀ u ∈ interior (Set.Ici (0 : ℝ)), deriv Φ u ≤ 0 := by
    intro u hu
    rw [interior_Ici] at hu
    rw [(hderiv u).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg
      (hoeffding_deriv_factor_nonpos p u hp0 hp1 (le_of_lt hu))
      (Real.exp_nonneg _)
  have hanti := antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont hdiff hderiv_nonpos
  have hle : Φ t ≤ Φ 0 := hanti (le_refl (0 : ℝ)) ht0 ht0
  have hΦ0 : Φ 0 = 1 := by
    dsimp [Φ]
    simp [Real.exp_zero]
  rw [hΦ0] at hle
  have hmul := mul_le_mul_of_nonneg_right hle (Real.exp_nonneg (t ^ 2 / 8))
  calc
    (1 - p + p * Real.exp t) * Real.exp (-p * t)
      = Φ t * Real.exp (t ^ 2 / 8) := by
        dsimp [Φ]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
    _ ≤ 1 * Real.exp (t ^ 2 / 8) := hmul
    _ = Real.exp (t ^ 2 / 8) := one_mul _

private lemma exp_affine_bound_on_unit_interval (u t : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp (t * u) ≤ 1 - u + u * Real.exp t := by
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
    (sub_nonneg.mpr hu1) hu0 (sub_add_cancel 1 u)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hconv
  rwa [mul_comm u t] at hconv

private lemma hoeffding_one_var {X : Type*} [Fintype X] [Nonempty X]
    (w : X → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∑ x : X, w x = 1)
    (h : X → ℝ) (hmean : ∑ x : X, w x * h x = 0) (hdiff : ∀ x y : X, h x - h y ≤ 1)
    (t : ℝ) (ht0 : 0 ≤ t) :
    ∑ x : X, w x * Real.exp (t * h x) ≤ Real.exp (t ^ 2 / 8) := by
  let a : ℝ := Finset.univ.inf' Finset.univ_nonempty h
  let p : ℝ := -a
  let u : X → ℝ := fun x => h x - a
  have hu0 : ∀ x : X, 0 ≤ u x := by
    intro x
    dsimp [u, a]
    exact sub_nonneg.mpr (Finset.inf'_le h (Finset.mem_univ x))
  have hu1 : ∀ x : X, u x ≤ 1 := by
    intro x
    dsimp [u, a]
    have hle : h x - 1 ≤ Finset.univ.inf' Finset.univ_nonempty h :=
      Finset.le_inf' Finset.univ_nonempty h (fun y _ => by linarith [hdiff x y])
    linarith
  have husum : ∑ x : X, w x * u x = p := by
    have h1 : (∑ x : X, w x * (h x - a)) = (∑ x : X, w x * h x) - (∑ x : X, w x) * a := by
      rw [Finset.sum_mul]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    dsimp [u, p]
    rw [h1, hmean, hw1]
    ring
  have hp0 : 0 ≤ p := by
    rw [← husum]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hw0 x) (hu0 x)
  have hp1 : p ≤ 1 := by
    rw [← husum, ← hw1]
    exact Finset.sum_le_sum fun x _ => mul_le_of_le_one_right (hw0 x) (hu1 x)
  have hpoint : ∀ x : X,
      w x * Real.exp (t * h x) ≤
        w x * (1 - u x + u x * Real.exp t) * Real.exp (-p * t) := by
    intro x
    have hhx : t * h x = t * u x + (-p * t) := by
      dsimp [u, p]
      ring
    rw [hhx, Real.exp_add, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg (-p * t))
    exact mul_le_mul_of_nonneg_left (exp_affine_bound_on_unit_interval (u x) t (hu0 x) (hu1 x)) (hw0 x)
  have hsum_le : ∑ x : X, w x * Real.exp (t * h x) ≤
      (∑ x : X, w x * (1 - u x + u x * Real.exp t)) * Real.exp (-p * t) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun x _ => hpoint x
  have hsum_eval : ∑ x : X, w x * (1 - u x + u x * Real.exp t) = 1 - p + p * Real.exp t := by
    have h1 : ∀ x : X, w x * (1 - u x + u x * Real.exp t) =
        w x - w x * u x + (w x * u x) * Real.exp t := fun x => by ring
    simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, husum]
  rw [hsum_eval] at hsum_le
  exact le_trans hsum_le (hoeffding_bernoulli_bound p t hp0 hp1 ht0)

private def prodWeight {X : Type*} (w : X → ℝ) {n : ℕ} (ω : Fin n → X) : ℝ :=
  ∏ j : Fin n, w (ω j)

private def prodExp {X : Type*} [Fintype X] (w : X → ℝ) (n : ℕ) (F : (Fin n → X) → ℝ) : ℝ :=
  ∑ ω : Fin n → X, prodWeight w ω * F ω

private lemma prodWeight_nonneg {X : Type*} (w : X → ℝ) (hw0 : ∀ x, 0 ≤ w x)
    {n : ℕ} (ω : Fin n → X) :
    0 ≤ prodWeight w ω :=
  Finset.prod_nonneg fun j _ => hw0 (ω j)

private lemma sum_prodWeight {X : Type*} [Fintype X] (w : X → ℝ) (hw1 : ∑ x : X, w x = 1)
    (n : ℕ) :
    ∑ ω : Fin n → X, prodWeight w ω = 1 := by
  unfold prodWeight
  rw [← (Fintype.prod_sum (fun (_ : Fin n) (x : X) => w x))]
  exact Finset.prod_eq_one fun _ _ => hw1

private lemma prodExp_const {X : Type*} [Fintype X] (w : X → ℝ) (hw1 : ∑ x : X, w x = 1)
    (n : ℕ) (c : ℝ) :
    prodExp w n (fun _ => c) = c := by
  unfold prodExp
  rw [← Finset.sum_mul, sum_prodWeight w hw1 n, one_mul]

private lemma prodExp_const_mul {X : Type*} [Fintype X] (w : X → ℝ) (n : ℕ)
    (c : ℝ) (F : (Fin n → X) → ℝ) :
    prodExp w n (fun ω => c * F ω) = c * prodExp w n F := by
  unfold prodExp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  ring

private lemma prodExp_mono {X : Type*} [Fintype X] (w : X → ℝ) (hw0 : ∀ x, 0 ≤ w x)
    (n : ℕ) {F G : (Fin n → X) → ℝ} (h : ∀ ω, F ω ≤ G ω) :
    prodExp w n F ≤ prodExp w n G := by
  unfold prodExp
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (prodWeight_nonneg w hw0 ω)

private def sliceAvg {X : Type*} [Fintype X] (w : X → ℝ) {n : ℕ}
    (F : (Fin (n + 1) → X) → ℝ) (ω : Fin n → X) : ℝ :=
  ∑ x : X, w x * F (Fin.cons x ω)

private lemma prodExp_succ {X : Type*} [Fintype X] (w : X → ℝ) (n : ℕ)
    (F : (Fin (n + 1) → X) → ℝ) :
    prodExp w (n + 1) F = prodExp w n (sliceAvg w F) := by
  unfold prodExp sliceAvg
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => X)).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold prodWeight
  dsimp [Fin.consEquiv]
  rw [Fin.prod_univ_succ, Fin.cons_zero]
  simp only [Fin.cons_succ]
  ring

private lemma fin_cons_update_zero {X : Type*} {n : ℕ} (x y : X) (ω : Fin n → X) :
    Function.update (Fin.cons x ω : Fin (n + 1) → X) 0 y = Fin.cons y ω := by
  ext j
  refine Fin.cases ?_ ?_ j
  · simp
  · intro i
    simp [Fin.succ_ne_zero]

private lemma fin_cons_update_succ {X : Type*} {n : ℕ} (x y : X) (ω : Fin n → X) (j : Fin n) :
    Function.update (Fin.cons x ω : Fin (n + 1) → X) j.succ y =
      Fin.cons x (Function.update ω j y) := by
  ext k
  refine Fin.cases ?_ ?_ k
  · simp [(Fin.succ_ne_zero j).symm]
  · intro i
    by_cases hij : i = j
    · subst hij
      simp
    · have hne : i.succ ≠ j.succ := Fin.succ_injective n |>.ne hij
      simp [hij, hne]

private lemma mcdiarmid_mgf_bound {X : Type*} [Fintype X] [Nonempty X]
    (w : X → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∑ x : X, w x = 1) (t : ℝ) (ht0 : 0 ≤ t) :
    ∀ (n : ℕ) (F : (Fin n → X) → ℝ),
      (∀ (ω : Fin n → X) (j : Fin n) (x y : X),
        F (Function.update ω j x) - F (Function.update ω j y) ≤ 1) →
      prodExp w n (fun ω => Real.exp (t * (F ω - prodExp w n F))) ≤
        Real.exp ((n : ℝ) * t ^ 2 / 8)
  | 0, F, _ => by
    have hconst : (fun ω : Fin 0 → X => Real.exp (t * (F ω - prodExp w 0 F))) = fun _ => 1 := by
      funext ω
      have hF : F = fun _ => F ω := by
        funext ω'
        congr 1
        exact Subsingleton.elim ω' ω
      have hE : prodExp w 0 F = F ω := by
        conv_lhs => rw [hF]
        exact prodExp_const w hw1 0 (F ω)
      rw [hE, sub_self, mul_zero, Real.exp_zero]
    rw [hconst, prodExp_const w hw1 0 1]
    simp
  | n + 1, F, hlip => by
    let G : (Fin n → X) → ℝ := sliceAvg w F
    have hEG : prodExp w (n + 1) F = prodExp w n G := prodExp_succ w n F
    have hGlip : ∀ (ω : Fin n → X) (j : Fin n) (u v : X),
        G (Function.update ω j u) - G (Function.update ω j v) ≤ 1 := by
      intro ω j u v
      dsimp [G, sliceAvg]
      rw [← Finset.sum_sub_distrib, ← hw1]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [← mul_sub, ← fin_cons_update_succ, ← fin_cons_update_succ]
      exact mul_le_of_le_one_right (hw0 x) (hlip (Fin.cons x ω) j.succ u v)
    have ih := mcdiarmid_mgf_bound w hw0 hw1 t ht0 n G hGlip
    rw [hEG, prodExp_succ w n]
    have hslice : ∀ ω : Fin n → X,
        sliceAvg w (fun ω' => Real.exp (t * (F ω' - prodExp w n G))) ω ≤
          Real.exp (t ^ 2 / 8) * Real.exp (t * (G ω - prodExp w n G)) := by
      intro ω
      let h : X → ℝ := fun x => F (Fin.cons x ω) - G ω
      have hmean : ∑ x : X, w x * h x = 0 := by
        dsimp [h]
        have h1 : (∑ x : X, w x * (F (Fin.cons x ω) - G ω)) =
            (∑ x : X, w x * F (Fin.cons x ω)) - (∑ x : X, w x) * G ω := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun x _ => by ring
        rw [h1, hw1, one_mul]
        dsimp [G, sliceAvg]
        ring
      have hdiff : ∀ x y : X, h x - h y ≤ 1 := by
        intro x y
        dsimp [h]
        have heq : (F (Fin.cons x ω) - G ω) - (F (Fin.cons y ω) - G ω) =
            F (Function.update (Fin.cons x ω : Fin (n + 1) → X) 0 x) -
              F (Function.update (Fin.cons x ω : Fin (n + 1) → X) 0 y) := by
          rw [fin_cons_update_zero, fin_cons_update_zero]
          ring
        rw [heq]
        exact hlip (Fin.cons x ω) 0 x y
      have hhoeff := hoeffding_one_var w hw0 hw1 h hmean hdiff t ht0
      have hfactor : sliceAvg w (fun ω' => Real.exp (t * (F ω' - prodExp w n G))) ω =
          (∑ x : X, w x * Real.exp (t * h x)) * Real.exp (t * (G ω - prodExp w n G)) := by
        unfold sliceAvg
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        dsimp [h]
        ring
      rw [hfactor]
      exact mul_le_mul_of_nonneg_right hhoeff (Real.exp_nonneg _)
    calc
      prodExp w n (sliceAvg w (fun ω' => Real.exp (t * (F ω' - prodExp w n G))))
        ≤ prodExp w n (fun ω => Real.exp (t ^ 2 / 8) * Real.exp (t * (G ω - prodExp w n G))) :=
          prodExp_mono w hw0 n hslice
      _ = Real.exp (t ^ 2 / 8) * prodExp w n (fun ω => Real.exp (t * (G ω - prodExp w n G))) :=
          prodExp_const_mul w n _ _
      _ ≤ Real.exp (t ^ 2 / 8) * Real.exp ((n : ℝ) * t ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _)
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * t ^ 2 / 8) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring

private instance isProbabilityMeasure_arrivalLaw {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (arrivalLaw ν n) := by
  unfold arrivalLaw
  infer_instance

private lemma arrivalLaw_real_singleton {X : Type} [Fintype X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    {n : ℕ} (ω : Fin n → X) :
    (arrivalLaw ν n).real {ω} = prodWeight (fun x => ν.real {x}) ω := by
  unfold arrivalLaw prodWeight
  have hset : ({ω} : Set (Fin n → X)) = Set.univ.pi (fun j : Fin n => {ω j}) := by
    ext ω'
    simp [funext_iff]
  simp only [measureReal_def, hset, Measure.pi_pi]
  exact ENNReal.toReal_prod _ _

private lemma integral_arrivalLaw_eq_prodExp {X : Type} [Fintype X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (n : ℕ) (F : (Fin n → X) → ℝ) :
    ∫ ω, F ω ∂(arrivalLaw ν n) = prodExp (fun x => ν.real {x}) n F := by
  rw [integral_fintype (Integrable.of_finite)]
  unfold prodExp
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [smul_eq_mul, arrivalLaw_real_singleton ν ω]

private lemma sum_measureReal_singleton {X : Type} [Fintype X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν] :
    ∑ x : X, ν.real {x} = 1 := by
  have h1 := integral_fintype (f := fun _ : X => (1 : ℝ)) (Integrable.of_finite (μ := ν))
  simp only [smul_eq_mul, mul_one, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one] at h1
  exact h1.symm

private lemma mcdiarmid_upper_tail {X : Type} [Fintype X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (n : ℕ) (F : (Fin n → X) → ℝ)
    (hlip : ∀ (ω : Fin n → X) (j : Fin n) (x y : X),
      F (Function.update ω j x) - F (Function.update ω j y) ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    (arrivalLaw ν n).real {ω | F ω - ∫ ω', F ω' ∂(arrivalLaw ν n) > (n : ℝ) * ε} ≤
      Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
  have : Nonempty X := Measure.nonempty_of_neZero ν
  let w : X → ℝ := fun x => ν.real {x}
  have hw0 : ∀ x : X, 0 ≤ w x := fun x => measureReal_nonneg
  have hw1 : ∑ x : X, w x = 1 := sum_measureReal_singleton ν
  let μF : ℝ := prodExp w n F
  have hμF : ∫ ω', F ω' ∂(arrivalLaw ν n) = μF := integral_arrivalLaw_eq_prodExp ν n F
  rw [hμF]
  let S : Set (Fin n → X) := {ω | F ω - μF > (n : ℝ) * ε}
  have hmeasS : MeasurableSet S := MeasurableSet.of_discrete
  have hind : (arrivalLaw ν n).real S = prodExp w n (S.indicator (fun _ => (1 : ℝ))) := by
    rw [← integral_indicator_one hmeasS, integral_arrivalLaw_eq_prodExp]
    rfl
  change (arrivalLaw ν n).real S ≤ Real.exp (-2 * (n : ℝ) * ε ^ 2)
  rw [hind]
  let t : ℝ := 4 * ε
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have hpoint : ∀ ω : Fin n → X,
      S.indicator (fun _ => (1 : ℝ)) ω ≤
        Real.exp (-t * ((n : ℝ) * ε)) * Real.exp (t * (F ω - μF)) := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, ← Real.exp_add]
      have hgt : (n : ℝ) * ε < F ω - μF := hω
      have hpos : 0 ≤ -t * ((n : ℝ) * ε) + t * (F ω - μF) := by
        have : 0 < t * (F ω - μF - (n : ℝ) * ε) := mul_pos (by dsimp [t]; linarith) (by linarith)
        linarith
      exact Real.one_le_exp hpos
    · rw [Set.indicator_of_notMem hω]
      exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
  have hmgf := mcdiarmid_mgf_bound w hw0 hw1 t ht0 n F hlip
  calc
    prodExp w n (S.indicator (fun _ => (1 : ℝ)))
      ≤ prodExp w n (fun ω => Real.exp (-t * ((n : ℝ) * ε)) * Real.exp (t * (F ω - μF))) :=
        prodExp_mono w hw0 n hpoint
    _ = Real.exp (-t * ((n : ℝ) * ε)) * prodExp w n (fun ω => Real.exp (t * (F ω - μF))) :=
        prodExp_const_mul w n _ _
    _ ≤ Real.exp (-t * ((n : ℝ) * ε)) * Real.exp ((n : ℝ) * t ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [t]
        ring

private def DiffByAtMostOneInsert {A : Type} [DecidableEq A] (W W' : Finset A) : Prop :=
  W' = W ∨ ∃ x, W' = insert x W

private lemma greedyStep_nil {A : Type} [DecidableEq A] (W : Finset A) :
    greedyStep W [] = W := rfl

private lemma diffByAtMostOneInsert_greedyStep_self {A : Type} [DecidableEq A]
    (W : Finset A) (l : List A) :
    DiffByAtMostOneInsert W (greedyStep W l) := by
  unfold greedyStep DiffByAtMostOneInsert
  cases l.find? (fun a => decide (a ∉ W)) with
  | none => left; rfl
  | some a => right; exact ⟨a, rfl⟩

private lemma find_not_mem_insert_of_none {A : Type} [DecidableEq A]
    (W : Finset A) (x : A) (l : List A)
    (h : l.find? (fun a => decide (a ∉ W)) = none) :
    l.find? (fun a => decide (a ∉ insert x W)) = none := by
  rw [List.find?_eq_none] at h ⊢
  intro a ha
  have h1 := h a ha
  simp only [decide_eq_true_eq, not_not] at h1 ⊢
  exact Finset.mem_insert_of_mem h1

private lemma find_not_mem_insert_of_some_ne {A : Type} [DecidableEq A]
    (W : Finset A) (x a : A) (l : List A)
    (h : l.find? (fun b => decide (b ∉ W)) = some a) (hne : a ≠ x) :
    l.find? (fun b => decide (b ∉ insert x W)) = some a := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    rw [List.find?_cons] at h ⊢
    by_cases hmem : hd ∈ W
    · have hd1 : decide (hd ∉ W) = false := decide_eq_false (not_not.mpr hmem)
      have hd2 : decide (hd ∉ insert x W) = false :=
        decide_eq_false (not_not.mpr (Finset.mem_insert_of_mem hmem))
      rw [hd1] at h
      rw [hd2]
      exact ih h
    · have hd1 : decide (hd ∉ W) = true := decide_eq_true hmem
      rw [hd1] at h
      injection h with hhd
      subst hhd
      have hd2 : decide (hd ∉ insert x W) = true :=
        decide_eq_true (by simp [Finset.mem_insert, hne, hmem])
      rw [hd2]

private lemma diffByAtMostOneInsert_greedyStep {A : Type} [DecidableEq A]
    {W W' : Finset A} (h : DiffByAtMostOneInsert W W') (l : List A) :
    DiffByAtMostOneInsert (greedyStep W l) (greedyStep W' l) := by
  rcases h with rfl | ⟨x, rfl⟩
  · left; rfl
  · cases hfind : l.find? (fun a => decide (a ∉ W)) with
    | none =>
      have h1 : greedyStep W l = W := by unfold greedyStep; rw [hfind]
      have h2 : greedyStep (insert x W) l = insert x W := by
        unfold greedyStep; rw [find_not_mem_insert_of_none W x l hfind]
      rw [h1, h2]
      exact Or.inr ⟨x, rfl⟩
    | some a =>
      have h1 : greedyStep W l = insert a W := by unfold greedyStep; rw [hfind]
      by_cases hax : a = x
      · subst hax
        rw [h1]
        exact diffByAtMostOneInsert_greedyStep_self (insert a W) l
      · have h2 : greedyStep (insert x W) l = insert a (insert x W) := by
          unfold greedyStep; rw [find_not_mem_insert_of_some_ne W x a l hfind hax]
        rw [h1, h2]
        exact Or.inr ⟨x, Finset.insert_comm a x W⟩

private lemma matchedAfter_update_eq_of_le {A : Type} [DecidableEq A] {n : ℕ}
    (ls : Fin n → List A) (t : Fin n) (j : ℕ) (hj : j ≤ t.val) :
    matchedAfter (Function.update ls t []) j = matchedAfter ls j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj_lt : j < t.val := Nat.lt_of_succ_le hj
    have hjn : j < n := Nat.lt_trans hj_lt t.isLt
    have hne : (⟨j, hjn⟩ : Fin n) ≠ t := by
      intro heq
      have : j = t.val := congrArg Fin.val heq
      omega
    simp [matchedAfter, hjn, ih (Nat.le_of_lt hj_lt), Function.update_of_ne hne]

private lemma diffByAtMostOneInsert_matchedAfter_update {A : Type} [DecidableEq A] {n : ℕ}
    (ls : Fin n → List A) (t : Fin n) (j : ℕ) :
    DiffByAtMostOneInsert (matchedAfter (Function.update ls t []) j) (matchedAfter ls j) := by
  induction j with
  | zero => exact Or.inl rfl
  | succ j ih =>
    simp only [matchedAfter]
    split_ifs with hjn
    · by_cases hjt : (⟨j, hjn⟩ : Fin n) = t
      · have hj_le : j ≤ t.val := by
          have : j = t.val := congrArg Fin.val hjt
          omega
        rw [matchedAfter_update_eq_of_le ls t j hj_le, hjt, Function.update_self, greedyStep_nil]
        exact diffByAtMostOneInsert_greedyStep_self (matchedAfter ls j) (ls t)
      · rw [Function.update_of_ne hjt]
        exact diffByAtMostOneInsert_greedyStep ih (ls ⟨j, hjn⟩)
    · exact ih

private lemma algValue_update_bounds {A : Type} [DecidableEq A] {n : ℕ}
    (ls : Fin n → List A) (t : Fin n) :
    algValue (Function.update ls t []) ≤ algValue ls ∧
      algValue ls ≤ algValue (Function.update ls t []) + 1 := by
  unfold algValue
  rcases diffByAtMostOneInsert_matchedAfter_update ls t n with h | ⟨x, h⟩
  · rw [h]
    exact ⟨le_refl _, Nat.le_succ _⟩
  · rw [h]
    exact ⟨Finset.card_le_card (Finset.subset_insert x _), Finset.card_insert_le x _⟩

private lemma alg_neg_lip {A X : Type} [DecidableEq A] {n : ℕ} (lst : X → List A)
    (ω : Fin n → X) (j : Fin n) (x y : X) :
    (-(ALG lst (Function.update ω j x) : ℝ)) - (-(ALG lst (Function.update ω j y) : ℝ)) ≤ 1 := by
  unfold ALG
  let lsx : Fin n → List A := fun k => lst (Function.update ω j x k)
  let lsy : Fin n → List A := fun k => lst (Function.update ω j y k)
  have hupd : Function.update lsy j [] = Function.update lsx j [] := by
    ext k
    by_cases hkj : k = j
    · subst hkj; simp
    · simp [lsx, lsy, hkj]
  have hx := algValue_update_bounds lsx j
  have hy := algValue_update_bounds lsy j
  rw [hupd] at hy
  have hle : algValue lsy ≤ algValue lsx + 1 := le_trans hy.2 (Nat.add_le_add_right hx.1 1)
  have hleR : (algValue lsy : ℝ) ≤ (algValue lsx : ℝ) + 1 := by exact_mod_cast hle
  linarith

theorem solution {A X : Type} [DecidableEq A] [Fintype X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν] (lst : X → List A)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (arrivalLaw ν n).real {ω | (ALG lst ω : ℝ) - expALG ν lst n < -((n : ℝ) * ε)} ≤
      Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
  let F : (Fin n → X) → ℝ := fun ω => -(ALG lst ω : ℝ)
  have hint : ∫ ω, F ω ∂(arrivalLaw ν n) = -expALG ν lst n := by
    unfold F expALG
    exact integral_neg (fun ω => (ALG lst ω : ℝ))
  have hset : {ω | (ALG lst ω : ℝ) - expALG ν lst n < -((n : ℝ) * ε)} =
      {ω | F ω - ∫ ω', F ω' ∂(arrivalLaw ν n) > (n : ℝ) * ε} := by
    ext ω
    change ((ALG lst ω : ℝ) - expALG ν lst n < -((n : ℝ) * ε)) ↔
      (F ω - ∫ ω', F ω' ∂(arrivalLaw ν n) > (n : ℝ) * ε)
    rw [hint]
    dsimp [F]
    constructor <;> intro h <;> linarith
  rw [hset]
  exact mcdiarmid_upper_tail ν n F (alg_neg_lip lst) ε hε

end
