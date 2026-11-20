-- Prove2me | solution 1 for TwoSAT.exact_tester
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-20T01:58:15.50808+00:00
-- url     : https://prove2.me/submissions/b6ad3647-1bc3-470a-8cf9-9dcf10d8cd30

import Definitions.Def_YoshidaTwoSAT_QueryModel
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Nodup
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Relation
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Sion

namespace TwoSAT
def MainClaim : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ ε ν : ℝ, 0 < ε → 0 < ν → ν < 1 / 2 →
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ (q : ℕ) (alg : PMF (Tree n d q)),
        (q : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ν) * (1 + Real.log n) ^ k ∧
        ∀ F : Input n d,
          (Satisfiable F.formula → rejection alg F = 0) ∧
          (ε * d * n ≤ distance F.formula → (2 / 3 : ENNReal) ≤ rejection alg F)

end TwoSAT

section

namespace TwoSAT.Weights

open MeasureTheory Set Finset
open scoped BigOperators

noncomputable def weight (c : ℝ) := min 1 (Real.exp (-c))
noncomputable def potential (c : ℝ) := if 0 ≤ c then Real.exp (-c) else 1 - c

theorem weight_pos (c : ℝ) : 0 < weight c := lt_min zero_lt_one (Real.exp_pos _)

theorem potential_eq (c : ℝ) : potential c = weight c + max (-c) 0 := by
  by_cases h : 0 ≤ c
  · simp [potential, weight, h]
  · have hc : 0 ≤ -c := by linarith
    simp [potential, weight, h, min_eq_left (Real.one_le_exp hc), max_eq_left hc, sub_eq_add_neg]

private noncomputable def intervalHit (a b x : ℝ) : ℝ :=
  (Ico a b).indicator (fun _ => (1 : ℝ)) x

private theorem average_intervals {E : Type*} [Fintype E] (lo hi : E → ℝ) {r A B : ℝ}
    (hr : 0 < r) (h : ∀ θ ∈ Icc 0 r, A ≤ B + ∑ i, intervalHit (lo i) (hi i) θ) :
    r * A ≤ r * B + ∑ i, max (hi i - lo i) 0 := by
  let S := Icc 0 r
  let μ : Measure ℝ := volume.restrict S
  have : IsFiniteMeasure μ := by dsimp [μ, S]; infer_instance
  have hI (i : E) : Integrable (intervalHit (lo i) (hi i)) μ :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Ico
  have hsum := integrable_finsetSum univ (fun i _ => hI i)
  have hmono := setIntegral_mono_on (μ := (volume : Measure ℝ)) (s := S)
    (f := fun _ => A) (g := fun θ => B + ∑ i, intervalHit (lo i) (hi i) θ)
    (show Integrable (fun _ => A) μ from integrable_const A)
    ((show Integrable (fun _ => B) μ from integrable_const B).add hsum)
    measurableSet_Icc h
  have hpart (i : E) : (∫ θ, intervalHit (lo i) (hi i) θ ∂μ) ≤ max (hi i - lo i) 0 := by
    unfold intervalHit
    rw [show (fun _ : ℝ => (1 : ℝ)) = 1 from rfl, integral_indicator_one measurableSet_Ico]
    have hh : μ.real (Ico (lo i) (hi i)) ≤ volume.real (Ico (lo i) (hi i)) := by
      apply ENNReal.toReal_mono (measure_Ico_lt_top.ne)
      exact Measure.restrict_le_self _
    exact hh.trans_eq Real.volume_real_Ico
  change (∫ _ in S, A) ≤ (∫ θ, B + ∑ i, intervalHit (lo i) (hi i) θ ∂μ) at hmono
  rw [integral_add (integrable_const B) hsum, integral_finsetSum univ (fun i _ => hI i)] at hmono
  change (∫ _ in S, A) ≤ (∫ _ in S, B) + _ at hmono
  simp only [S, setIntegral_const, Real.volume_real_Icc_of_le hr.le, sub_zero,
    smul_eq_mul] at hmono
  exact hmono.trans (add_le_add le_rfl (sum_le_sum fun i _ => hpart i))

variable {V : Type}

noncomputable def score (z : V → ℝ) (a : Literal V) := if a.sign then z a.var else -z a.var

noncomputable def rounded (z : V → ℝ) (t : V → Bool) (θ : ℝ) (x : V) : Bool :=
  if θ < |z x| then decide (z x < 0) else t x

private theorem retained {z : V → ℝ} {t : V → Bool} {θ : ℝ} {a : Literal V}
    (h : |score z a| ≤ θ) : a.eval (rounded z t θ) = a.eval t := by
  rcases a with ⟨x, s⟩; cases s <;> simp_all [score, rounded, Literal.eval]

private theorem assigned {z : V → ℝ} {t : V → Bool} {θ : ℝ} {a : Literal V}
    (hθ : 0 ≤ θ) (h : θ < |score z a|) (hv : a.eval (rounded z t θ) = true) :
    score z a < -θ := by
  rcases a with ⟨x, s⟩
  cases s <;> simp only [score, Bool.false_eq_true, if_false, if_true, abs_neg] at * <;>
    simp_all [Literal.eval, rounded, abs_eq_max_neg, max_def] <;> split_ifs at * <;> grind

/-- Weight charged to a forbidden pair when both endpoints evaluate to true. -/
noncomputable def charge (w : ℝ) (t : V → Bool) (a b : Literal V) : ℝ :=
  if a.eval t && b.eval t then w else 0

private theorem clause_bound (z : V → ℝ) (t : V → Bool) (a b : Literal V) {θ r : ℝ}
    (ht : θ ∈ Icc 0 r) :
    charge 1 (rounded z t θ) a b ≤
      Real.exp (2*r) * charge (weight (score z a + score z b)) t a b +
        intervalHit (max (score z a) (score z b)) (-(min (score z a) (score z b))) θ := by
  have hw : 0 ≤ charge (weight (score z a + score z b)) t a b := by
    unfold charge; split_ifs <;> first | exact (weight_pos _).le | rfl
  have hhit : 0 ≤ intervalHit (max (score z a) (score z b)) (-(min (score z a) (score z b))) θ := by
    unfold intervalHit; apply Set.indicator_nonneg; simp
  by_cases hab : a.eval (rounded z t θ) = true ∧ b.eval (rounded z t θ) = true
  · simp only [charge, hab.1, hab.2, Bool.and_self, if_true]
    by_cases hsmall : |score z a| ≤ θ ∧ |score z b| ≤ θ
    · have ha := (retained (t := t) hsmall.1).symm.trans hab.1
      have hb := (retained (t := t) hsmall.2).symm.trans hab.2
      simp only [ha, hb, Bool.and_self, if_true]
      have hr : 0 ≤ r := ht.1.trans ht.2
      have hlow : Real.exp (-(2*r)) ≤ weight (score z a + score z b) := by
        apply le_min
        · apply Real.exp_le_one_iff.mpr; linarith
        · apply Real.exp_le_exp.mpr
          linarith [le_abs_self (score z a), le_abs_self (score z b), hsmall.1, hsmall.2, ht.2]
      have hprod := mul_le_mul_of_nonneg_left hlow (Real.exp_pos (2*r)).le
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hprod
      linarith
    · have hu (c : Literal V) (h : c.eval (rounded z t θ) = true) : score z c ≤ θ := by
        by_cases hx : θ < |score z c|
        · linarith [assigned ht.1 hx h, ht.1]
        · exact (le_abs_self _).trans (le_of_not_gt hx)
      have hm : θ < -(min (score z a) (score z b)) := by
        by_cases hx : θ < |score z a|
        · linarith [assigned ht.1 hx hab.1, min_le_left (score z a) (score z b)]
        · have hy : θ < |score z b| := by grind
          linarith [assigned ht.1 hy hab.2, min_le_right (score z a) (score z b)]
      have hi : θ ∈ Ico (max (score z a) (score z b)) (-(min (score z a) (score z b))) :=
        ⟨max_le (hu a hab.1) (hu b hab.2), hm⟩
      rw [intervalHit, Set.indicator_of_mem hi]
      exact le_add_of_nonneg_left (mul_nonneg (Real.exp_pos _).le hw)
  · have hz : charge 1 (rounded z t θ) a b = 0 := by simp [charge, hab]
    rw [hz]
    exact add_nonneg (mul_nonneg (Real.exp_pos _).le hw) hhit

/-- Lemma 3.1. Each clause is indexed by its two forbidden literals. -/
theorem weighted_loss {E : Type*} [Fintype E] (u v : E → Literal V) (z : V → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (far : ∀ t : V → Bool, δ * Fintype.card E ≤ ∑ i, charge 1 t (u i) (v i))
    (budget : ∑ i, potential (score z (u i) + score z (v i)) ≤ Fintype.card E)
    (t : V → Bool) :
    δ / 2 * Real.exp (-4 / δ) * Fintype.card E ≤
      ∑ i, charge (weight (score z (u i) + score z (v i))) t (u i) (v i) := by
  let r := 2 / δ
  let L := ∑ i, charge (weight (score z (u i) + score z (v i))) t (u i) (v i)
  have hr : 0 < r := by dsimp [r]; positivity
  have hp := average_intervals (fun i => max (score z (u i)) (score z (v i)))
    (fun i => -(min (score z (u i)) (score z (v i)))) (A := δ * Fintype.card E)
    (B := Real.exp (2*r) * L) hr (by
      intro θ hθ
      apply (far (rounded z t θ)).trans
      dsimp [L]
      rw [mul_sum, ← sum_add_distrib]
      exact sum_le_sum fun i _ => clause_bound z t (u i) (v i) hθ)
  have hclip (a b : ℝ) : max (-(min a b) - max a b) 0 ≤ potential (a + b) := by
    rw [potential_eq]
    have hh : -(min a b) - max a b = -(a+b) := by grind
    rw [hh]; linarith [weight_pos (a+b)]
  have hsum := (sum_le_sum (s := univ) (fun i _ => hclip (score z (u i)) (score z (v i)))).trans budget
  have hrd : r * δ = 2 := by dsimp [r]; field_simp
  have hscale : 2*r = 4/δ := by dsimp [r]; ring
  rw [hscale] at hp
  have hmult := mul_le_mul_of_nonneg_left hp hδ.le
  have hsum' := mul_le_mul_of_nonneg_left hsum hδ.le
  have hweight : δ / 2 * Fintype.card E ≤ Real.exp (4/δ) * L := by
    nlinarith only [hmult, hsum', congrArg (fun x => x * (δ * (Fintype.card E : ℝ))) hrd,
      congrArg (fun x => x * (Real.exp (4/δ) * L)) hrd]
  change _ ≤ L
  have hfactor : -4 / δ = -(4/δ) := by ring
  rw [hfactor, Real.exp_neg]
  calc
    _ = (δ / 2 * Fintype.card E) / Real.exp (4/δ) := by ring
    _ ≤ L := (div_le_iff₀ (Real.exp_pos _)).mpr (by linarith only [hweight])

/-- The total weight has the same lower bound as the loss of an assignment. -/
theorem total_weight {E : Type*} [Fintype E] (u v : E → Literal V) (z : V → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (far : ∀ t : V → Bool, δ * Fintype.card E ≤ ∑ i, charge 1 t (u i) (v i))
    (budget : ∑ i, potential (score z (u i) + score z (v i)) ≤ Fintype.card E) :
    δ / 2 * Real.exp (-4 / δ) * Fintype.card E ≤
      ∑ i, weight (score z (u i) + score z (v i)) := by
  apply (weighted_loss u v z δ hδ far budget (fun _ => false)).trans
  apply sum_le_sum
  intro i _
  unfold charge
  split_ifs
  · rfl
  · exact (weight_pos _).le

end TwoSAT.Weights

end

section

namespace TwoSAT.Weights

open Filter Set

private theorem weight_exp (x : ℝ) : weight x = Real.exp (-(max x 0)) := by
  rcases le_total x 0 with h | h
  · simp [weight, h]
  · simp [weight, h]

private theorem exp_difference {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp (-a) - Real.exp (-b) ≤ b-a := by
  have h := Real.add_one_le_exp (a-b)
  have hpos : 0 ≤ 1 - Real.exp (a-b) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hs : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hh := mul_le_mul_of_nonneg_right hs hpos
  have he : Real.exp (-a) * Real.exp (a-b) = Real.exp (-b) := by rw [← Real.exp_add]; ring_nf
  nlinarith only [h, hh, he]

theorem weight_lipschitz (x y : ℝ) : |weight x - weight y| ≤ |x-y| := by
  wlog hxy : x ≤ y generalizing x y
  · simpa only [abs_sub_comm] using this y x (le_of_not_ge hxy)
  have hle : max x 0 ≤ max y 0 := max_le_max hxy le_rfl
  have hmono : weight y ≤ weight x := by simpa [weight_exp] using (neg_le_neg hle)
  rw [abs_of_nonneg (sub_nonneg.mpr hmono), abs_of_nonpos (sub_nonpos.mpr hxy), weight_exp, weight_exp]
  have he := exp_difference (le_max_right x 0) hle
  grind

theorem potential_hasDerivAt (x : ℝ) : HasDerivAt potential (-weight x) x := by
  have lin (y : ℝ) : HasDerivAt (fun t : ℝ => 1-t) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub 1
  have expo (y : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-y)) y := by
    simpa using (hasDerivAt_id y).neg.exp
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [weight_exp, max_eq_right hx.le, neg_zero, Real.exp_zero]
    apply (lin x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact if_neg (not_le.mpr hy)
  · rw [weight_exp]; simp only [max_self, neg_zero, Real.exp_zero]
    apply hasDerivWithinAt_univ.mp
    rw [← Iic_union_Ici (a := (0 : ℝ))]
    apply HasDerivWithinAt.union
    · apply (lin 0).hasDerivWithinAt.congr_of_mem _ (by simp : (0 : ℝ) ∈ Iic 0)
      intro t ht
      rcases (show t ≤ 0 from ht).lt_or_eq with h | rfl
      · exact if_neg (not_le.mpr h)
      · simp [potential]
    · have he : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-1) 0 := by simpa using expo 0
      exact he.hasDerivWithinAt.congr_of_mem (fun _ ht => if_pos ht) (by simp : (0 : ℝ) ∈ Ici 0)
  · rw [weight_exp, max_eq_left hx.le]
    apply (expo x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact if_pos (le_of_lt hy)

/-- Scalar smoothness inequality behind equation (7). -/
theorem potential_descent (x y : ℝ) :
    potential y ≤ potential x - weight x * (y-x) + (y-x)^2/2 := by
  let f (t : ℝ) := potential t + weight x * (t-x) - (t-x)^2/2
  have derivF (t : ℝ) : HasDerivAt f (-weight t + weight x - (t-x)) t := by
    have h := (hasDerivAt_id t).sub_const x
    apply (((potential_hasDerivAt t).add (h.const_mul (weight x))).sub
      ((h.pow 2).div_const 2)).congr_deriv
    simp
  have hd : Differentiable ℝ f := fun t => (derivF t).differentiableAt
  have hmax : f y ≤ f x := by
    rcases le_total x y with h | h
    · apply antitoneOn_of_deriv_nonpos (convex_Ici x) hd.continuous.continuousOn
        hd.differentiableOn _ (le_refl x) h h
      intro t ht
      have hxt : x ≤ t := mem_Ici.mp (interior_subset ht)
      rw [(derivF t).deriv]
      have hh := (abs_le.mp (weight_lipschitz x t)).2
      rw [abs_of_nonpos (sub_nonpos.mpr hxt)] at hh
      linarith
    · apply monotoneOn_of_deriv_nonneg (convex_Iic x) hd.continuous.continuousOn
        hd.differentiableOn _ h (le_refl x) h
      intro t ht
      have htx : t ≤ x := mem_Iic.mp (interior_subset ht)
      rw [(derivF t).deriv]
      have hh := (abs_le.mp (weight_lipschitz x t)).1
      rw [abs_of_nonneg (sub_nonneg.mpr htx)] at hh
      linarith
  simp [f] at hmax
  linarith

end TwoSAT.Weights

end

section

namespace TwoSAT.Weights

open Finset
open scoped BigOperators

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]

def signOf (a : Literal V) : ℝ := if a.sign then 1 else -1

noncomputable def clauseScore (u v : E → Literal V) (z : V → ℝ) (i : E) :=
  score z (u i) + score z (v i)

noncomputable def energy (u v : E → Literal V) (z : V → ℝ) :=
  ∑ i, potential (clauseScore u v z i)

noncomputable def imbalance (u v : E → Literal V) (w : E → ℝ) (x : V) :=
  ∑ i, ((if (u i).var = x then signOf (u i) else 0) +
    (if (v i).var = x then signOf (v i) else 0)) * w i

/-- Each clause contributes one occurrence at each endpoint. -/
def occurrences (u v : E → Literal V) (x : V) : ℕ :=
  ∑ i, ((if (u i).var = x then 1 else 0) + (if (v i).var = x then 1 else 0))

omit [Fintype V] [DecidableEq V] in
private theorem score_mul (a : Literal V) (z : V → ℝ) : score z a = signOf a * z a.var := by
  cases a with | mk x s => cases s <;> simp [score, signOf]

theorem adjoint (u v : E → Literal V) (w : E → ℝ) (h : V → ℝ) :
    ∑ i, w i * clauseScore u v h i = ∑ x, imbalance u v w x * h x := by
  classical
  simp only [imbalance, sum_mul, clauseScore, score_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp [add_mul, sum_add_distrib, ite_mul, mul_add]
  ring

omit [Fintype V] [DecidableEq V] in
private theorem score_sq (a : Literal V) (h : V → ℝ) : (score h a)^2 = (h a.var)^2 := by
  cases a with | mk x s => cases s <;> simp [score]

private theorem incidence_bound (u v : E → Literal V) (h : V → ℝ) {D : ℕ}
    (hd : ∀ x, occurrences u v x ≤ D) :
    ∑ i, (clauseScore u v h i)^2 ≤ 2 * D * ∑ x, (h x)^2 := by
  have rows : ∑ x, (occurrences u v x : ℝ) * (h x)^2 =
      ∑ i, ((h (u i).var)^2 + (h (v i).var)^2) := by
    simp only [occurrences, Nat.cast_sum, Nat.cast_add, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    simp [add_mul, sum_add_distrib, apply_ite Nat.cast, ite_mul]
  calc
    _ ≤ ∑ i, 2 * ((h (u i).var)^2 + (h (v i).var)^2) := by
      apply sum_le_sum
      intro i _
      unfold clauseScore
      rw [← score_sq (u i) h, ← score_sq (v i) h]
      nlinarith only [sq_nonneg (score h (u i) - score h (v i))]
    _ = 2 * ∑ x, (occurrences u v x : ℝ) * (h x)^2 := by rw [← mul_sum, rows]
    _ ≤ 2 * ∑ x, (D : ℝ) * (h x)^2 := by
      gcongr with x
      exact_mod_cast hd x
    _ = _ := by rw [← mul_sum, mul_assoc]

noncomputable def step (u v : E → Literal V) (D : ℕ) (z : V → ℝ) (x : V) :=
  z x + imbalance u v (fun i => weight (clauseScore u v z i)) x / (2 * D)

/-- Equation (7), the descent of the full clause potential in one parallel update. -/
theorem energy_step (u v : E → Literal V) {D : ℕ} (hD : 0 < D)
    (hd : ∀ x, occurrences u v x ≤ D) (z : V → ℝ) :
    energy u v (step u v D z) +
      (∑ x, (imbalance u v (fun i => weight (clauseScore u v z i)) x)^2) / (4 * D)
      ≤ energy u v z := by
  let w i := weight (clauseScore u v z i)
  let b := imbalance u v w
  let h x := b x / (2 * D)
  have diff (i : E) : clauseScore u v (step u v D z) i - clauseScore u v z i =
      clauseScore u v h i := by
    have hstep (x : V) : step u v D z x = z x + h x := rfl
    simp only [clauseScore, score_mul, hstep]
    ring
  have scalar (i : E) := potential_descent (clauseScore u v z i) (clauseScore u v (step u v D z) i)
  have scalar' (i : E) : potential (clauseScore u v (step u v D z) i) ≤
      potential (clauseScore u v z i) - w i * clauseScore u v h i + (clauseScore u v h i)^2 / 2 := by
    simpa only [diff] using scalar i
  have H := sum_le_sum (s := univ) (fun i _ => scalar' i)
  simp only [sum_add_distrib, sum_sub_distrib, ← sum_div, adjoint] at H
  have hdpos : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have cross : ∑ x, b x * h x = (∑ x, (b x)^2) / (2 * D) := by
    rw [sum_div]; apply sum_congr rfl; intro x _; dsimp [h]; ring
  have square : ∑ x, (h x)^2 = (∑ x, (b x)^2) / (2 * D)^2 := by
    simp [h, div_pow, sum_div]
  change energy u v (step u v D z) ≤ energy u v z - ∑ x, b x * h x +
    (∑ i, (clauseScore u v h i)^2) / 2 at H
  rw [cross] at H
  have mat := incidence_bound u v h hd
  rw [square] at mat
  change _ + (∑ x, (b x)^2) / (4 * D) ≤ _
  have alg : 2 * (D : ℝ) * ((∑ x, (b x)^2) / (2 * D)^2) =
      (∑ x, (b x)^2) / (2 * D) := by field_simp
  rw [alg] at mat
  linarith only [H, mat, show (∑ x, (b x)^2) / (4 * (D : ℝ)) =
    ((∑ x, (b x)^2) / (2 * D)) / 2 by ring]

noncomputable def iterate (u v : E → Literal V) (D : ℕ) : ℕ → V → ℝ
  | 0 => fun _ => 0
  | j + 1 => step u v D (iterate u v D j)

/-- Telescoping descent, retaining both the final potential and the cumulative imbalance. -/
theorem iterate_budget (u v : E → Literal V) {D : ℕ} (hD : 0 < D)
    (hd : ∀ x, occurrences u v x ≤ D) (T : ℕ) :
    energy u v (iterate u v D T) +
      ∑ j ∈ range T, (∑ x, (imbalance u v
        (fun i => weight (clauseScore u v (iterate u v D j) i)) x)^2) / (4 * D)
      ≤ Fintype.card E := by
  induction T with
  | zero =>
    simp [iterate, energy, clauseScore, score_mul, potential]
  | succ T ih =>
    rw [sum_range_succ]
    have h := energy_step u v hD hd (iterate u v D T)
    simp only [iterate] at ⊢
    linarith

end TwoSAT.Weights

end

section

namespace TwoSAT.Weights

open Finset
open scoped BigOperators

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]

noncomputable def roundWeight (u v : E → Literal V) (D j : ℕ) (i : E) :=
  weight (clauseScore u v (iterate u v D j) i)

noncomputable def averageWeight (u v : E → Literal V) (D T : ℕ) (i : E) :=
  (∑ j ∈ range T, roundWeight u v D j i) / T

omit [Fintype V] [DecidableEq V] in
private theorem energy_nonneg (u v : E → Literal V) (z : V → ℝ) : 0 ≤ energy u v z :=
  sum_nonneg fun i _ => by
    rw [potential_eq]
    exact add_nonneg (weight_pos _).le (le_max_right _ _)

private theorem square_budget (u v : E → Literal V) {D : ℕ} (hD : 0 < D)
    (hd : ∀ x, occurrences u v x ≤ D) (T : ℕ) :
    ∑ j ∈ range T, ∑ x, (imbalance u v (roundWeight u v D j) x)^2 ≤
    (4 * D : ℝ) * Fintype.card E := by
  have h := iterate_budget u v hD hd T
  rw [← sum_div] at h
  have pos : (0 : ℝ) < 4 * D := by positivity
  rw [mul_comm]; apply (div_le_iff₀ pos).mp
  unfold roundWeight
  linarith only [h, energy_nonneg u v (iterate u v D T)]

omit [Fintype V] in
private theorem linear_average (u v : E → Literal V) (D T : ℕ) (x : V) :
    imbalance u v (averageWeight u v D T) x =
    (∑ j ∈ range T, imbalance u v (roundWeight u v D j) x) / T := by
  simp only [imbalance, averageWeight, ← mul_div_assoc, mul_sum, sum_div]
  rw [sum_comm]

omit [Fintype V] in
private theorem absent {u v : E → Literal V} {x : V} (h : occurrences u v x = 0) (w : E → ℝ) :
    imbalance u v w x = 0 := by
  have hi (i : E) : ((if (u i).var = x then 1 else 0) + (if (v i).var = x then 1 else 0) : ℕ) = 0 :=
    (sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp h i (mem_univ _)
  apply sum_eq_zero
  intro i _
  specialize hi i
  split_ifs at hi ⊢ <;> simp_all

private theorem total_occurrences (u v : E → Literal V) :
    ∑ x, occurrences u v x = 2 * Fintype.card E := by
  unfold occurrences
  rw [sum_comm]
  simp [sum_add_distrib, two_mul, mul_two]

/-- Equation (10) in squared form, valid even with arbitrarily many isolated variables. -/
theorem average_imbalance (u v : E → Literal V) {D T : ℕ} (hD : 0 < D)
    (hd : ∀ x, occurrences u v x ≤ D) (hT : 0 < T) :
    (∑ x, |imbalance u v (averageWeight u v D T) x|)^2 ≤
      (Fintype.card E : ℝ)^2 * (8 * D / T) := by
  let b (j : ℕ) := imbalance u v (roundWeight u v D j)
  let w := averageWeight u v D T
  let active (x : V) : ℝ := if occurrences u v x = 0 then 0 else 1
  have hs (x : V) : active x * |imbalance u v w x| = |imbalance u v w x| := by
    by_cases hx : occurrences u v x = 0
    · simp [active, hx, absent hx]
    · simp [active, hx]
  have hcount : ∑ x, (active x)^2 ≤ 2 * (Fintype.card E : ℝ) := by
    have heq : (∑ x, (occurrences u v x : ℝ)) = 2 * Fintype.card E := by exact_mod_cast total_occurrences u v
    rw [← heq]
    apply sum_le_sum
    intro x _
    dsimp [active]
    split_ifs with hx
    · simp [hx]
    · simp only [one_pow]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr hx
  have hspace := sum_mul_sq_le_sq_mul_sq univ active (fun x => |imbalance u v w x|)
  simp only [hs, sq_abs] at hspace
  have htime (x : V) : (imbalance u v w x)^2 ≤ (∑ j ∈ range T, (b j x)^2) / T := by
    have h := sum_mul_sq_le_sq_mul_sq (range T) (fun _ => (1 : ℝ)) (fun j => b j x)
    simp only [one_mul, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at h
    rw [show imbalance u v w x = (∑ j ∈ range T, b j x) / T from linear_average .., div_pow]
    have ht : (0 : ℝ) < T := by exact_mod_cast hT
    apply (div_le_iff₀ (sq_pos_of_pos ht)).mpr
    convert h using 1
    field_simp
  have htotal : ∑ x, (imbalance u v w x)^2 ≤ ((4 * D : ℝ) * Fintype.card E) / T := by
    apply (sum_le_sum (fun x _ => htime x)).trans
    rw [← sum_div, sum_comm]
    exact div_le_div_of_nonneg_right (square_budget u v hD hd T) (Nat.cast_nonneg _)
  calc
    _ ≤ _ := hspace
    _ ≤ (2 * (Fintype.card E : ℝ)) * ((4 * D * Fintype.card E) / T) :=
      mul_le_mul hcount htotal (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
    _ = _ := by ring

/-- Averaging preserves the loss guarantee for each fixed assignment. -/
theorem average_loss (u v : E → Literal V) {D T : ℕ} (hD : 0 < D)
    (hd : ∀ x, occurrences u v x ≤ D) (hT : 0 < T) {δ : ℝ} (hδ : 0 < δ)
    (far : ∀ t : V → Bool, δ * Fintype.card E ≤ ∑ i, charge 1 t (u i) (v i)) (t : V → Bool) :
    δ / 2 * Real.exp (-4 / δ) * Fintype.card E ≤
      ∑ i, charge (averageWeight u v D T i) t (u i) (v i) := by
  have each (j : ℕ) := weighted_loss u v (iterate u v D j) δ hδ far (by
    have h := iterate_budget u v hD hd j
    apply le_trans _ h
    apply le_add_of_nonneg_right
    exact sum_nonneg fun k _ => div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)) t
  have row (i : E) : charge (averageWeight u v D T i) t (u i) (v i) =
      (∑ j ∈ range T, charge (roundWeight u v D j i) t (u i) (v i)) / T := by
    unfold charge averageWeight; split_ifs <;> simp
  simp_rw [row]
  rw [← sum_div, sum_comm]
  apply (le_div_iff₀ (show (0 : ℝ) < T by exact_mod_cast hT)).mpr
  simpa [roundWeight, clauseScore, mul_comm (T : ℝ)] using sum_le_sum (s := range T) (fun j _ => each j)

omit [Fintype V] in
private theorem avg_bounds (u v : E → Literal V) (D : ℕ) {T : ℕ} (hT : 0 < T) (i : E) :
    0 < averageWeight u v D T i ∧ averageWeight u v D T i ≤ 1 := by
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  constructor
  · apply div_pos _ ht
    apply sum_pos (fun j _ => weight_pos _) ⟨0, mem_range.mpr hT⟩
  · apply (div_le_iff₀ ht).mpr
    simpa [roundWeight,weight] using sum_le_sum (s := range T) (fun j _ => min_le_left 1 (Real.exp
      (-(clauseScore u v (iterate u v D j) i))))

/-- The quantitative weight, imbalance and loss guarantees of Theorem 3.2.
The vector is the explicit average of the first T parallel updates. -/
theorem weight_guarantees (u v : E → Literal V) {D T : ℕ} (hD : 0 < D)
    (hd : ∀ x, occurrences u v x ≤ D) {δ β : ℝ} (hδ : 0 < δ) (hβ : 0 < β)
    (hm : 0 < Fintype.card E)
    (far : ∀ t : V → Bool, δ * Fintype.card E ≤ ∑ i, charge 1 t (u i) (v i))
    (k : ℝ) (hk : k = δ / 4 * Real.exp (-4 / δ))
    (time : 288 * (D : ℝ) / (k^2 * β^2) ≤ T) :
    let w := averageWeight u v D T
    let W := ∑ i, w i
    (∀ i, 0 < w i ∧ w i ≤ 1) ∧ k * Fintype.card E ≤ W ∧
      (∑ x, |imbalance u v w x|) / W ≤ β ∧
      ∀ t, k / 2 ≤ (∑ i, charge (w i) t (u i) (v i)) / W := by
  let w := averageWeight u v D T
  let W := ∑ i, w i
  let m : ℝ := Fintype.card E
  have hkpos : 0 < k := by rw [hk]; positivity
  have hmpos : 0 < m := by dsimp [m]; exact_mod_cast hm
  have ht : (0 : ℝ) < T := lt_of_lt_of_le (by positivity) time
  have hT : 0 < T := by exact_mod_cast ht
  have hw := avg_bounds u v D hT
  have hl (t : V → Bool) : 2*k*m ≤ ∑ i, charge (w i) t (u i) (v i) := by
    have hac := average_loss u v hD hd hT hδ far t
    convert hac using 1
    dsimp [m]; rw [hk]; ring
  have upper : W ≤ m := by simpa [W, m] using sum_le_sum (s := univ) (fun i _ => (hw i).2)
  have lower : 2*k*m ≤ W := by
    apply (hl (fun _ => false)).trans
    apply sum_le_sum
    intro i _
    unfold charge
    split_ifs <;> first | rfl | exact (hw i).1.le
  have hW : 0 < W := lt_of_lt_of_le (by positivity) lower
  have hWk : k*m ≤ W := by linarith only [lower, mul_pos hkpos hmpos]
  refine ⟨hw, hWk, (div_le_iff₀ hW).mpr ?_, fun t => (le_div_iff₀ hW).mpr ?_⟩
  · have ht' := (div_le_iff₀ (by positivity)).mp time
    have hscale : 8 * (D : ℝ) / T ≤ k^2 * β^2 := (div_le_iff₀ ht).mpr (by
      nlinarith only [ht', show 0 ≤ (D : ℝ) by positivity])
    have hs := average_imbalance u v hD hd hT
    have hs' : (∑ x, |imbalance u v w x|)^2 ≤ (β * (k*m))^2 := by
      calc
        _ ≤ m^2 * (8 * D / T) := hs
        _ ≤ m^2 * (k^2 * β^2) := mul_le_mul_of_nonneg_left hscale (sq_nonneg _)
        _ = _ := by ring
    have hlin : (∑ x, |imbalance u v w x|) ≤ β * (k*m) :=
      le_of_sq_le_sq hs' (by positivity)
    exact hlin.trans (mul_le_mul_of_nonneg_left hWk hβ.le)
  · have low := hl t
    nlinarith only [low, mul_le_mul_of_nonneg_left upper hkpos.le, mul_pos hkpos hmpos]

end TwoSAT.Weights

end

section

namespace TwoSAT.Query

variable {n d : ℕ} {α β : Type}

/-- An oracle computation of cost at most k can be followed by any decision tree. -/
def Bounded (k : ℕ) (f : Oracle n d → α) : Prop :=
  ∀ (q : ℕ) (next : α → Tree n d q), ∃ tree : Tree n d (q+k),
    ∀ o, tree.run o = (next (f o)).run o

theorem pure (a : α) : Bounded (n := n) (d := d) 0 (fun _ => a) :=
  fun _ next => ⟨next a, fun _ => rfl⟩

theorem read (x : Fin n) (i : Fin d) : Bounded 1 (fun o : Oracle n d => o x i) :=
  fun _ next => ⟨.ask x i next, fun _ => rfl⟩

theorem bind {j k : ℕ} {f : Oracle n d → α} {g : α → Oracle n d → β}
    (hf : Bounded j f) (hg : ∀ a, Bounded k (g a)) :
    Bounded (j+k) (fun o => g (f o) o) := by
  intro q next
  choose trees ht using fun a => hg a q next
  obtain ⟨tr, htr⟩ := hf (q+k) trees
  have h : (q+k)+j = q+(j+k) := by omega
  rw [← h]
  exact ⟨tr, fun o => (htr o).trans (ht _ o)⟩

theorem map {k : ℕ} {f : Oracle n d → α} (hf : Bounded k f) (g : α → β) :
    Bounded k (fun o => g (f o)) := fun q next => hf q (next ∘ g)

/-- Query each entry once. The answer at each index can itself require k queries. -/
theorem gather {k : ℕ} (m : ℕ) (f : Fin m → Oracle n d → α)
    (hf : ∀ i, Bounded k (f i)) : Bounded (m*k) (fun o i => f i o) := by
  induction m with
  | zero =>
    have h : (fun o i => f i o) = (fun _ => (Fin.elim0 : Fin 0 → α)) := by
      funext o i; exact i.elim0
    rw [h, Nat.zero_mul]
    exact pure _
  | succ m ih =>
    have tail := ih (fun i => f i.succ) (fun i => hf i.succ)
    let prepend (a : α) (v : Fin m → α) : Fin (m+1) → α := Fin.cons a v
    have head (a : α) : Bounded (m*k) (fun o => prepend a (fun i => f i.succ o)) :=
      map tail (prepend a)
    have h := bind (g := fun a o => prepend a (fun i => f i.succ o)) (hf 0) head
    have eq : (fun o => prepend (f 0 o) (fun i => f i.succ o)) = (fun o i => f i o) := by
      funext o i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [eq] at h
    simpa only [Nat.succ_mul, Nat.add_comm k] using h

theorem decision {k : ℕ} {f : Oracle n d → Bool} (hf : Bounded k f) :
    ∃ tr : Tree n d k, ∀ o, tr.run o = f o := by
  rw [← Nat.zero_add k]
  exact hf 0 (fun b => Tree.leaf b)

end TwoSAT.Query

end

section

namespace TwoSAT.Reduction

variable {V : Type}

/-- The second coordinate distinguishes original (false) and auxiliary (true) variables. -/
def liftLit (a : Literal V) : Literal (V × Bool) := ⟨(a.var, false), a.sign⟩

def gadget (a : Literal V) (s : Bool) : Clause (V × Bool) :=
  .pair (liftLit a) ⟨(a.var, true), s⟩

def expand : Clause V → List (Clause (V × Bool))
  | .unit a => [gadget a true, gadget a false]
  | .taut _ => []
  | .pair a b => [.pair (liftLit a) (liftLit b)]

def reduce (F : List (Clause V)) := F.flatMap expand

def restrict (t : V × Bool → Bool) (x : V) := t (x, false)

theorem clauseLoss (t : V × Bool → Bool) (c : Clause V) :
    loss t (expand c) = (if c.eval (restrict t) then 0 else 1) := by
  cases c with
  | taut => rfl
  | pair a b => simp [expand, loss, Clause.eval, Literal.eval, liftLit, restrict]
  | unit a =>
    rcases a with ⟨x, s⟩
    cases ho : t (x, false) <;> cases hz : t (x, true) <;> cases s <;>
      simp [expand, gadget, liftLit, loss, restrict, Clause.eval, Literal.eval, ho, hz]

private theorem loss_append (t : V → Bool) (F G : List (Clause V)) :
    loss t (F ++ G) = loss t F + loss t G := by
  induction F with
  | nil => simp [loss]
  | cons c cs ih => simp [loss, ih, Nat.add_assoc]

theorem loss_reduce (t : V × Bool → Bool) (F : List (Clause V)) :
    loss t (reduce F) = loss (restrict t) F := by
  induction F with
  | nil => rfl
  | cons c cs ih =>
    change loss t (expand c ++ reduce cs) = _
    simp only [loss_append, clauseLoss, ih, loss]

theorem attainableLosses (F : List (Clause V)) :
    Set.range (fun t => loss t (reduce F)) = Set.range (fun t => loss t F) := by
  ext k
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨restrict t, (loss_reduce t F).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨fun v => t v.1, loss_reduce _ F⟩

theorem distance_reduce (F : List (Clause V)) : distance (reduce F) = distance F := by
  unfold distance
  rw [attainableLosses]

theorem satisfiable_reduce (F : List (Clause V)) : Satisfiable (reduce F) ↔ Satisfiable F := by
  change 0 ∈ Set.range (fun t => loss t (reduce F)) ↔ 0 ∈ Set.range (fun t => loss t F)
  rw [attainableLosses]

theorem far_reduce (F : List (Clause V)) (ε : ℝ) (d n : ℕ)
    (h : ε * d * n ≤ distance F) :
    ε / 4 * (2 * (d : ℝ)) * (2 * (n : ℝ)) ≤ distance (reduce F) := by
  rw [distance_reduce]
  linarith only [h]

/-- Destination slots have indices (original slot, second half). -/
def slot (aux second : Bool) : Option (Clause V) → Option (Clause (V × Bool))
  | none | some (.taut _) => none
  | some (.unit a) => some (gadget a (!second))
  | some (.pair a b) =>
    if aux || second then none else some (.pair (liftLit a) (liftLit b))

/-- Each call consults one original incidence slot. -/
def reducedOracle {I : Type} (oracle : V → I → Option (Clause V))
    (v : V × Bool) (i : I × Bool) : Option (Clause (V × Bool)) :=
  slot v.2 i.2 (oracle v.1 i.1)

theorem slot_origin {aux second : Bool} {input : Option (Clause V)} {c}
    (h : slot aux second input = some c) : ∃ d, input = some d ∧ c ∈ expand d := by
  cases input with
  | none => simp [slot] at h
  | some d =>
    refine ⟨d, rfl, ?_⟩
    cases d <;> cases aux <;> cases second <;> simp_all [slot, expand]

/-- Clauses retained from a rejecting transcript can be traced back to an
unsatisfiable set of original clauses. -/
theorem unsat_origins {F : List (Clause V)} {G : List (Clause (V × Bool))}
    (origin : ∀ c ∈ G, c ∈ reduce F) (bad : ¬ Satisfiable G) : ¬ Satisfiable F := by
  intro sat
  obtain ⟨t, ht⟩ := (satisfiable_reduce F).mpr sat
  apply bad
  exact ⟨t, (loss_eq_zero_iff t G).mpr fun c hc =>
    (loss_eq_zero_iff t (reduce F)).mp ht c (origin c hc)⟩

end TwoSAT.Reduction

end

section

namespace TwoSAT.Reduction

variable {V I : Type}

/-- The tags of a replacement clause identify its source and its half-slot. -/
private def origin (c : Clause (V × Bool)) : Option (Clause V × Bool) :=
  match c with
  | .pair a b =>
    let u : Literal V := ⟨a.var.1, a.sign⟩
    if b.var.2 then some (.unit u, !b.sign)
    else some (.pair u ⟨b.var.1, b.sign⟩, false)
  | _ => none

private theorem origin_expand {c : Clause V} {e} (h : e ∈ expand c) :
    ∃ s, origin e = some (c, s) := by
  cases c with
  | taut => simp [expand] at h
  | unit a =>
    simp only [expand, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  | pair a b =>
    simp only [expand, List.mem_singleton] at h
    subst e
    exact ⟨false, rfl⟩

theorem nodup_reduce {F : List (Clause V)} (hF : F.Nodup) : (reduce F).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro c _
    cases c <;> simp [expand, gadget]
  · apply hF.imp
    intro a b hn e ha hb
    obtain ⟨i, hi⟩ := origin_expand ha
    obtain ⟨j, hj⟩ := origin_expand hb
    exact hn (congrArg Prod.fst (Option.some.inj (hi.symm.trans hj)))

private theorem slot_spec {x : V} {aux s : Bool} {c : Clause V} {e}
    (hc : c.incident x) (hs : slot aux s (some c) = some e) :
    e ∈ expand c ∧ e.incident (x, aux) ∧ origin e = some (c, s) := by
  cases c with
  | taut => simp [slot] at hs
  | unit a =>
    change x = a.var at hc
    subst x
    cases aux <;> cases s <;> simp [slot] at hs <;> subst e <;> simp [expand, Clause.incident, gadget, liftLit, origin]
  | pair a b =>
    cases aux <;> cases s <;> simp [slot] at hs
    subst e
    simpa [expand, Clause.incident, liftLit, origin] using hc

private theorem slot_exists {x : V} {aux : Bool} {c : Clause V} {e}
    (he : e ∈ expand c) (hx : e.incident (x, aux)) :
    c.incident x ∧ ∃ s, slot aux s (some c) = some e := by
  cases c with
  | taut => simp [expand] at he
  | unit a =>
    simp only [expand, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;>
      cases aux <;> simp_all [Clause.incident, liftLit, gadget, slot]
  | pair a b =>
    simp only [expand, List.mem_singleton] at he
    subst e
    cases aux <;> simp_all [Clause.incident, liftLit, slot]

/-- Every non-null answer is an incident clause of the reduced formula. -/
theorem oracle_sound {F : List (Clause V)} {o : V → I → Option (Clause V)}
    (hs : ∀ x i c, o x i = some c → c ∈ F ∧ c.incident x)
    (v : V × Bool) (i : I × Bool) (e)
    (h : reducedOracle o v i = some e) : e ∈ reduce F ∧ e.incident v := by
  unfold reducedOracle at h
  cases hi : o v.1 i.1 with
  | none => simp [hi, slot] at h
  | some c =>
    rw [hi] at h
    obtain ⟨hm, hx⟩ := hs _ _ _ hi
    obtain ⟨he, hv, _⟩ := slot_spec hx h
    exact ⟨List.mem_flatMap.mpr ⟨c, hm, he⟩, hv⟩

/-- Each incident output clause appears exactly once at the queried variable. -/
theorem oracle_coverage {F : List (Clause V)} {o : V → I → Option (Clause V)}
    (hs : ∀ x i c, o x i = some c → c ∈ F ∧ c.incident x)
    (hc : ∀ x c, c ∈ F → c.incident x → ∃! i, o x i = some c)
    (v : V × Bool) (e) (he : e ∈ reduce F) (hv : e.incident v) :
    ∃! i, reducedOracle o v i = some e := by
  obtain ⟨c, hm, hce⟩ := List.mem_flatMap.mp he
  obtain ⟨hx, s, hslot⟩ := slot_exists hce hv
  obtain ⟨i, hi, unique⟩ := hc v.1 c hm hx
  refine ⟨(i, s), by simpa [reducedOracle, hi] using hslot, ?_⟩
  rintro ⟨j, t⟩ hj
  change slot v.2 t (o v.1 j) = some e at hj
  cases ho : o v.1 j with
  | none => simp [ho, slot] at hj
  | some d =>
    rw [ho] at hj
    have h1 := (slot_spec hx hslot).2.2
    have h2 := (slot_spec (hs _ _ _ ho).2 hj).2.2
    have hh := Option.some.inj (h2.symm.trans h1)
    have hd := congrArg Prod.fst hh
    have ht := congrArg Prod.snd hh
    exact Prod.ext (unique j (by simpa using ho.trans (congrArg some hd))) ht

end TwoSAT.Reduction

end

section

namespace TwoSAT

variable {V W : Type}

def Literal.rename (f : V → W) (a : Literal V) : Literal W := ⟨f a.var, a.sign⟩

def Clause.rename (f : V → W) : Clause V → Clause W
  | .unit a => .unit (a.rename f)
  | .taut x => .taut (f x)
  | .pair a b => .pair (a.rename f) (b.rename f)

@[simp] theorem rename_eval (f : V → W) (t : W → Bool) (c : Clause V) :
    (c.rename f).eval t = c.eval (t ∘ f) := by cases c <;> rfl

@[simp] theorem rename_loss (f : V → W) (F : List (Clause V)) (t : W → Bool) :
    loss t (F.map (Clause.rename f)) = loss (t ∘ f) F := by
  induction F with
  | nil => rfl
  | cons c cs ih => simp [loss, ih]

theorem rename_distance (e : V ≃ W) (F : List (Clause V)) :
    distance (F.map (Clause.rename e)) = distance F := by
  unfold distance
  congr 1
  ext k
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t ∘ e, (rename_loss e F t).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t ∘ e.symm, ?_⟩
    simp [Function.comp_def]

namespace Reduction

/-- Number each original variable first, then its auxiliary copy. The same
bijection labels the two sets of incidence slots. -/
def labels (n : ℕ) : (Fin n × Bool) ≃ Fin (n + n) where
  toFun v := finSumFinEquiv (if v.2 then Sum.inr v.1 else Sum.inl v.1)
  invFun i := (finSumFinEquiv.symm i).elim (fun x => (x, false)) (fun x => (x, true))
  left_inv := by rintro ⟨x, b⟩; cases b <;> simp only [Equiv.symm_apply_apply] <;> rfl
  right_inv := by
    intro i
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective i
    cases y <;> simp only [Equiv.symm_apply_apply] <;> rfl

def doubledAnswer {n} (aux second : Bool) (a : Answer n) : Answer (n + n) :=
  (slot aux second a).map (Clause.rename (labels n))

def doubledOracle {n d} (o : Oracle n d) : Oracle (n + n) (d + d) :=
  fun x i =>
    let v := (labels n).symm x
    let j := (labels d).symm i
    doubledAnswer v.2 j.2 (o v.1 j.1)

private theorem rename_back (f : V ≃ W) (c : Clause V) :
    (c.rename f).rename f.symm = c := by
  cases c <;> simp [Clause.rename, Literal.rename]

theorem rename_inj (f : V ≃ W) : Function.Injective (Clause.rename f) := by
  intro a b h
  simpa only [rename_back] using congrArg (Clause.rename f.symm) h

theorem rename_incident (f : V ≃ W) (c : Clause V) (x : V) :
    (c.rename f).incident (f x) ↔ c.incident x := by
  cases c <;> simp [Clause.rename, Literal.rename, Clause.incident]

theorem expanded_pair {n d} (F : Input n d) {c} (hc : c ∈ reduce F.formula) :
    ∃ a b, c.rename (labels n) = .pair a b ∧ a.var < b.var := by
  obtain ⟨u, hu, he⟩ := List.mem_flatMap.mp hc
  have hcan := F.canonical u hu
  cases u with
  | taut => simp [expand] at he
  | unit l =>
    simp only [expand, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> refine ⟨_, _, rfl, ?_⟩ <;>
      change l.var.val < n + l.var.val <;> omega
  | pair a b =>
    simp only [expand, List.mem_singleton] at he
    subst c
    exact ⟨_, _, rfl, hcan⟩

theorem query_label {n d} (F : Input n d) (v : Fin n × Bool) (i : Fin d × Bool) :
    doubledOracle F.oracle (labels n v) (labels d i) =
      (reducedOracle F.oracle v i).map (Clause.rename (labels n)) := by
  simp [doubledOracle, doubledAnswer, reducedOracle]

def doubledInput {n d} (F : Input n d) : Input (n + n) (d + d) where
  formula := (reduce F.formula).map (Clause.rename (labels n))
  distinct := (nodup_reduce F.distinct).map (rename_inj _)
  canonical := by
    intro c hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
    obtain ⟨a, b, hg, hlt⟩ := expanded_pair F he
    rw [hg]
    exact hlt
  oracle := doubledOracle F.oracle
  sound := by
    intro x i c h
    obtain ⟨v, rfl⟩ := (labels n).surjective x
    obtain ⟨j, rfl⟩ := (labels d).surjective i
    rw [query_label] at h
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hf, hx⟩ := oracle_sound F.sound v j e he
    exact ⟨List.mem_map.mpr ⟨e, hf, rfl⟩, (rename_incident _ _ _).mpr hx⟩
  coverage := by
    intro x c hm hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    obtain ⟨v, rfl⟩ := (labels n).surjective x
    have hv := (rename_incident _ _ _).mp hx
    obtain ⟨j, hj, hun⟩ := oracle_coverage F.sound F.coverage v e he hv
    refine ⟨labels d j, by simp [query_label, hj], ?_⟩
    intro i hi
    obtain ⟨k, rfl⟩ := (labels d).surjective i
    rw [query_label] at hi
    obtain ⟨e', h', heq⟩ := Option.map_eq_some_iff.mp hi
    have := rename_inj (labels n) heq
    subst e'
    exact congrArg (labels d) (hun k h')

theorem doubled_exact {n d} (F : Input n d) : Exact (doubledInput F) := by
  intro c hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  exact expanded_pair F he

theorem doubled_distance {n d} (F : Input n d) :
    distance (doubledInput F).formula = distance F.formula :=
  (rename_distance _ _).trans (distance_reduce _)

theorem doubled_satisfiable {n d} (F : Input n d) (hs : Satisfiable F.formula) :
    Satisfiable (doubledInput F).formula := by
  obtain ⟨t, ht⟩ := (satisfiable_reduce _).mpr hs
  refine ⟨t ∘ (labels n).symm, ?_⟩
  simpa [doubledInput, Function.comp_def] using ht

/-- Compile a decision tree on the doubled incidence table into one on the
original labels, preserving the query budget in the type. -/
def simulate {n d} : {q : ℕ} → Tree (n + n) (d + d) q → Tree n d q
  | _, .leaf b => .leaf b
  | _, .ask x i next =>
    let v := (labels n).symm x
    let j := (labels d).symm i
    .ask v.1 j.1 (fun a => simulate (next (doubledAnswer v.2 j.2 a)))

theorem run_simulate {n d q} (o : Oracle n d) (tree : Tree (n + n) (d + d) q) :
    (simulate tree).run o = tree.run (doubledOracle o) := by
  induction tree with
  | leaf => rfl
  | ask x i next ih => apply ih

theorem simulate_distribution {n d q} (o : Oracle n d)
    (p : PMF (Tree (n + n) (d + d) q)) :
    (p.map simulate).map (fun t => t.run o) = p.map (fun t => t.run (doubledOracle o)) := by
  rw [PMF.map_comp]
  simp only [Function.comp_def, run_simulate]

end Reduction
end TwoSAT

end

section

namespace TwoSAT.LocalWeights

open Finset TwoSAT.Weights

variable {n d : ℕ}

abbrev Edges (F : Input n d) := ↥F.formula.toFinset

/-- The gradient uses the two literals whose simultaneous truth violates the clause. -/
def forbidden {V} : Clause V → Literal V × Literal V
  | .pair a b => (a.flip, b.flip)
  | .unit a => (a.flip, a.flip)
  | .taut x => (⟨x, false⟩, ⟨x, true⟩)

def left (F : Input n d) (c : Edges F) := (forbidden c.val).1
def right (F : Input n d) (c : Edges F) := (forbidden c.val).2

instance (c : Clause (Fin n)) (x : Fin n) : Decidable (c.incident x) := by
  cases c <;> unfold Clause.incident <;> infer_instance

/-- Rewrite a sum over the occupied slots as a sum over the incident clauses. -/
theorem sum_slots {M : Type} [AddCommMonoid M] (F : Input n d) (x : Fin n)
    (f : Clause (Fin n) → M) :
    (∑ i, ((F.oracle x i).map f).getD 0) =
      ∑ c : Edges F, if c.val.incident x then f c.val else 0 := by
  classical
  have expand (i : Fin d) : ((F.oracle x i).map f).getD 0 =
      ∑ c : Edges F, if F.oracle x i = some c.val then f c.val else 0 := by
    cases h : F.oracle x i with
    | none => simp
    | some a =>
      let e : Edges F := ⟨a, List.mem_toFinset.mpr (F.sound _ _ _ h).1⟩
      have he (c : Edges F) : (a = c.val) ↔ c = e := by simp [e, Subtype.ext_iff, eq_comm]
      simp [he, e]
  simp_rw [expand]
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  by_cases hc : c.val.incident x
  · obtain ⟨j, hj, unique⟩ := F.coverage x _ (List.mem_toFinset.mp c.property) hc
    have he (i : Fin d) : F.oracle x i = some c.val ↔ i = j :=
      ⟨fun hi => unique i hi, fun h => h ▸ hj⟩
    simp [hc, he]
  · have he (i : Fin d) : F.oracle x i ≠ some c.val := fun h => hc (F.sound _ _ _ h).2
    simp [hc, he]

def neighbor (x : Fin n) : Answer n → Fin n
  | some (.pair a b) => if a.var = x then b.var else a.var
  | _ => x

noncomputable def signedValue {V} (a : Literal V) (t : ℝ) := if a.sign then t else -t

/-- Contribution of a single slot, using the current values at the two endpoints. -/
noncomputable def contribution (x : Fin n) : Answer n → ℝ → ℝ → ℝ
  | some (.pair a b), self, other =>
      if a.var = x then signOf a.flip * weight (signedValue a.flip self + signedValue b.flip other)
      else signOf b.flip * weight (signedValue a.flip other + signedValue b.flip self)
  | _, _, _ => 0

private theorem row_imbalance (F : Input n d) (exactF : Reduction.Exact F) (x : Fin n)
    (z : Fin n → ℝ) :
    (∑ i, contribution x (F.oracle x i) (z x) (z (neighbor x (F.oracle x i)))) =
      imbalance (left F) (right F) (fun e => weight (clauseScore (left F) (right F) z e)) x := by
  let f (c : Clause (Fin n)) := contribution x (some c) (z x) (z (neighbor x (some c)))
  have hi (i : Fin d) : contribution x (F.oracle x i) (z x) (z (neighbor x (F.oracle x i))) =
      ((F.oracle x i).map f).getD 0 := by cases F.oracle x i <;> rfl
  simp_rw [hi]
  rw [sum_slots]
  apply sum_congr rfl
  intro c _
  obtain ⟨a,b,h,hab⟩ := exactF c.val (List.mem_toFinset.mp c.property)
  have hne := hab.ne
  simp only [f, h, Clause.incident, left, right, forbidden, clauseScore, contribution,
    neighbor, signedValue, score, Literal.flip]
  by_cases ha : a.var = x
  · have hb : b.var ≠ x := fun he => hne (ha.trans he.symm)
    simp [ha, hb, Ne.symm hb]
  · by_cases hb : b.var = x
    · simp [ha, hb, Ne.symm ha]
    · simp [ha, hb, Ne.symm ha, Ne.symm hb]

/-- Recover the coordinate history at a root from the histories at its neighbors. -/
noncomputable def update (x : Fin n) (row : Fin d → Answer n) (child : Fin d → ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | j+1 =>
      let self := update x row child j
      self + (∑ i, contribution x (row i) self (child i j)) / (2*d)

noncomputable def history : ℕ → Fin n → Oracle n d → ℕ → ℝ
  | 0, _, _ => fun _ => 0
  | k+1, x, o => update x (o x) (fun i => history k (neighbor x (o x i)) o)

/-- The recursion queries d slots at the root, then explores each of the d children. -/
def queryCost (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => d + d * queryCost d k

theorem queryCost_bound {d : ℕ} (hd : 2 ≤ d) (k : ℕ) :
    queryCost d k + 2 ≤ 2 * d^k := by
  induction k with
  | zero => simp [queryCost]
  | succ k ih =>
    have h := Nat.mul_le_mul_left d ih
    simp only [queryCost, pow_succ]
    nlinarith only [h, hd]

theorem history_cost (k : ℕ) (x : Fin n) :
    Query.Bounded (queryCost d k) (history (d := d) k x) := by
  induction k generalizing x with
  | zero => exact Query.pure _
  | succ k ih =>
    have rows : Query.Bounded d (fun o : Oracle n d => o x) := by
      simpa using Query.gather d (fun i o => o x i) (fun i => Query.read x i)
    apply Query.bind (g := fun row o => update x row
      (fun i => history k (neighbor x (row i)) o)) rows
    intro row
    exact Query.map (Query.gather d _ (fun i => ih (neighbor x (row i)))) (update x row)

theorem history_correct (F : Input n d) (exactF : Reduction.Exact F) (k j : ℕ) (hj : j ≤ k)
    (x : Fin n) : history k x F.oracle j = iterate (left F) (right F) d j x := by
  induction k generalizing j x with
  | zero => have : j = 0 := by omega
            subst j; rfl
  | succ k ih =>
    induction j with
    | zero => rfl
    | succ j stepIH =>
      have hjk : j ≤ k := by omega
      have self := stepIH (by omega)
      change update x (F.oracle x) _ j = _ at self
      change update x (F.oracle x) _ (j+1) = _
      simp only [update, self, ih _ hjk, row_imbalance F exactF, iterate, step]

noncomputable def localWeight (d T : ℕ) (a b : Literal (Fin n)) (o : Oracle n d) : ℝ :=
  (∑ j ∈ range T, weight (signedValue a (history T a.var o j) +
    signedValue b (history T b.var o j))) / T

theorem localWeight_cost (d T : ℕ) (a b : Literal (Fin n)) :
    Query.Bounded (queryCost d T + queryCost d T) (localWeight d T a b) := by
  apply Query.bind (g := fun ha o =>
    (∑ j ∈ range T, weight (signedValue a (ha j) + signedValue b (history T b.var o j))) / T)
    (history_cost (d := d) T a.var)
  intro ha
  exact Query.map (history_cost T b.var) (fun hb =>
    (∑ j ∈ range T, weight (signedValue a (ha j) + signedValue b (hb j))) / T)

theorem localWeight_correct (F : Input n d) (exactF : Reduction.Exact F) (T : ℕ) (e : Edges F) :
    localWeight d T (left F e) (right F e) F.oracle = averageWeight (left F) (right F) d T e := by
  unfold localWeight averageWeight
  congr 1
  apply sum_congr rfl
  intro j hj
  simp only [history_correct F exactF T j (mem_range.mp hj).le, roundWeight, clauseScore,
    signedValue, score]

end TwoSAT.LocalWeights

end

section

namespace TwoSAT.LocalWeights

open Finset TwoSAT.Weights

variable {n d : ℕ}

theorem occurrence_bound (F : Input n d) (hF : Reduction.Exact F) (x : Fin n) :
    occurrences (left F) (right F) x ≤ d := by
  have slot := sum_slots (M := ℕ) F x (fun _ => 1)
  have hc : occurrences (left F) (right F) x = ∑ e : Edges F,
      if e.val.incident x then 1 else 0 := by
    apply sum_congr rfl
    intro e _
    obtain ⟨a,b,he,hab⟩ := hF e.val (List.mem_toFinset.mp e.property)
    simp only [left, right, he, forbidden, Literal.flip, Clause.incident]
    by_cases ha : a.var = x <;> by_cases hb : b.var = x <;> simp_all [eq_comm]
  rw [hc, ← slot]
  have h (i : Fin d) : ((F.oracle x i).map (fun _ => 1)).getD 0 ≤ (1 : ℕ) := by
    cases F.oracle x i <;> simp
  simpa using sum_le_sum (s := univ) (fun i _ => h i)

theorem edge_count_bound (F : Input n d) (hF : Reduction.Exact F) :
    Fintype.card (Edges F) ≤ d*n := by
  have total : (∑ x, occurrences (left F) (right F) x) = Fintype.card (Edges F) * 2 := by
    unfold occurrences; rw [sum_comm]; simp [sum_add_distrib]
  have h := sum_le_sum (s := univ) (fun x _ => occurrence_bound F hF x)
  simp only [total, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  calc
    Fintype.card (Edges F) ≤ Fintype.card (Edges F)*2 := by omega
    _ ≤ _ := by simpa [Nat.mul_comm d n] using h

private theorem loss_finset (t : Fin n → Bool) (cs : List (Clause (Fin n))) (hcs : cs.Nodup) :
    (loss t cs : ℝ) = ∑ c ∈ cs.toFinset, if c.eval t then (0 : ℝ) else 1 := by
  induction cs with
  | nil => simp [loss]
  | cons c cs ih =>
    have hd := List.nodup_cons.mp hcs
    simp [loss, hd.1, ih hd.2, apply_ite Nat.cast]

theorem edge_loss (F : Input n d) (hF : Reduction.Exact F) (t : Fin n → Bool) :
    (loss t F.formula : ℝ) = ∑ e : Edges F, charge 1 t (left F e) (right F e) := by
  classical
  rw [loss_finset _ _ F.distinct, ← sum_attach]
  apply sum_congr rfl
  intro e _
  obtain ⟨a,b,he,hab⟩ := hF e.val (List.mem_toFinset.mp e.property)
  cases ha : a.eval t <;> cases hb : b.eval t <;> simp [left, right, he, forbidden, Clause.eval, charge, ha, hb]

theorem far_edge_loss (F : Input n d) (hF : Reduction.Exact F) {ε : ℝ} (hε : 0 ≤ ε)
    (far : ε * d * n ≤ distance F.formula) (t : Fin n → Bool) :
    ε * Fintype.card (Edges F) ≤ ∑ e : Edges F, charge 1 t (left F e) (right F e) := by
  rw [← edge_loss F hF t]
  have hc : (Fintype.card (Edges F) : ℝ) ≤ (d : ℝ)*n := by exact_mod_cast edge_count_bound F hF
  have hd : distance F.formula ≤ loss t F.formula := Nat.sInf_le ⟨t, rfl⟩
  calc
    _ ≤ ε * ((d : ℝ)*n) := mul_le_mul_of_nonneg_left hc hε
    _ ≤ distance F.formula := by simpa [mul_assoc] using far
    _ ≤ _ := by exact_mod_cast hd

theorem distance_le_edges (F : Input n d) (hF : Reduction.Exact F) :
    (distance F.formula : ℝ) ≤ Fintype.card (Edges F) := by
  let t (_ : Fin n) := false
  have hd : distance F.formula ≤ loss t F.formula := Nat.sInf_le ⟨t,rfl⟩
  have hl (e : Edges F) : charge 1 t (left F e) (right F e) ≤ 1 := by
    unfold charge; split_ifs <;> norm_num
  calc
    _ ≤ (loss t F.formula : ℝ) := by exact_mod_cast hd
    _ = _ := edge_loss F hF t
    _ ≤ _ := by simpa using sum_le_sum (s := univ) (fun e _ => hl e)

/-- Theorem 3.2 in the incidence-slot model. The round count and query budget are
chosen before the input size, the formula, and its slot ordering. -/
theorem local_weight_theorem (d : ℕ) (hd : 0 < d) (ε β : ℝ) (hε : 0 < ε) (hβ : 0 < β) :
    let k := ε / 4 * Real.exp (-4/ε)
    ∃ T q : ℕ,
      (∀ n (a b : Literal (Fin n)), Query.Bounded q (localWeight d T a b)) ∧
      ∀ n, 0 < n → ∀ F : Input n d, Reduction.Exact F → ε*d*n ≤ distance F.formula →
        let w (e : Edges F) := localWeight d T (left F e) (right F e) F.oracle
        let W := ∑ e, w e
        (∀ e, 0 < w e ∧ w e ≤ 1) ∧ k * Fintype.card (Edges F) ≤ W ∧
        (∑ x, |imbalance (left F) (right F) w x|)/W ≤ β ∧
        ∀ t, k/2 ≤ (∑ e, charge (w e) t (left F e) (right F e))/W := by
  let k := ε / 4 * Real.exp (-4/ε)
  let T := ⌈288*(d : ℝ)/(k^2*β^2)⌉₊
  refine ⟨T,queryCost d T + queryCost d T,fun n a b => localWeight_cost d T a b,?_⟩
  intro n hn F hF far
  have pos : (0 : ℝ) < Fintype.card (Edges F) :=
    (show 0 < ε * (d : ℝ) * n by positivity).trans_le (far.trans (distance_le_edges F hF))
  have hm : 0 < Fintype.card (Edges F) := by exact_mod_cast pos
  have ret := weight_guarantees (left F) (right F) hd (occurrence_bound F hF) hε hβ hm
    (far_edge_loss F hF hε.le far) k rfl (Nat.le_ceil _ : 288*(d : ℝ)/(k^2*β^2) ≤ T)
  simpa only [localWeight_correct F hF] using ret

end TwoSAT.LocalWeights

end

section

namespace TwoSAT.Reassignment

open Finset MeasureTheory Set TwoSAT.Weights

variable {V E : Type} [Fintype E]

noncomputable def choose (z : V → ℝ) (t : V → Bool) (θ : ℝ) (x : V) :=
  if θ < |z x| then decide (0 < z x) else t x

private theorem retained (z : V → ℝ) (t : V → Bool) (θ : ℝ) (a : Literal V)
    (h : |score z a| ≤ θ) : a.eval (choose z t θ) = a.eval t := by
  rcases a with ⟨x, s⟩; cases s <;> simp_all [score, choose, Literal.eval]

private theorem assigned (z : V → ℝ) (t : V → Bool) {θ : ℝ} (hθ : 0 ≤ θ) (a : Literal V)
    (h : θ < |score z a|) (ht : a.eval (choose z t θ) = true) : θ < score z a := by
  rcases a with ⟨x,s⟩
  cases s <;> simp_all [score, choose, Literal.eval, abs_eq_max_neg, max_def] <;> split_ifs at * <;> grind

private noncomputable def hit (a b θ : ℝ) := (Set.Icc a b).indicator (fun _ => (1 : ℝ)) θ

private theorem hit_pos (a b θ : ℝ) : 0 ≤ hit a b θ :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) _

private theorem clause_cover (z : V → ℝ) (t : V → Bool) (a b : Literal V) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 1) :
    charge 1 (choose z t θ) a b ≤
      charge 1 t a b * hit (max |score z a| |score z b|) 1 θ +
      hit (-(min (score z a) (score z b))) (max (score z a) (score z b)) θ := by
  by_cases hv : a.eval (choose z t θ) = true ∧ b.eval (choose z t θ) = true
  · simp only [charge, hv.1, hv.2, Bool.and_self, if_true]
    by_cases hr : max |score z a| |score z b| ≤ θ
    · obtain ⟨ha,hb⟩ := max_le_iff.mp hr
      have h1 := (retained z t θ a ha).symm.trans hv.1
      have h2 := (retained z t θ b hb).symm.trans hv.2
      simp only [h1,h2,Bool.and_self,if_true,one_mul]
      rw [hit, Set.indicator_of_mem (show θ ∈ Set.Icc _ 1 from ⟨hr,hθ.2⟩)]
      linarith [hit_pos (-(min (score z a) (score z b))) (max (score z a) (score z b)) θ]
    · have low (c : Literal V) (hc : c.eval (choose z t θ) = true) : -θ ≤ score z c := by
        by_cases h : θ < |score z c|
        · linarith [assigned z t hθ.1 c h hc,hθ.1]
        · linarith [neg_abs_le (score z c),le_of_not_gt h]
      have hh : θ < max (score z a) (score z b) := by
        by_cases ha : θ < |score z a|
        · exact (assigned z t hθ.1 a ha hv.1).trans_le (le_max_left ..)
        · have hb : θ < |score z b| := by grind
          exact (assigned z t hθ.1 b hb hv.2).trans_le (le_max_right ..)
      have st : θ ∈ Set.Icc (-(min (score z a) (score z b))) (max (score z a) (score z b)) :=
        ⟨by linarith [le_min (low a hv.1) (low b hv.2)], hh.le⟩
      rw [show hit _ _ θ = 1 from Set.indicator_of_mem st _]
      split_ifs <;> simp [hit_pos]
  · simp only [charge, Bool.and_eq_true, if_neg hv]
    split_ifs <;> simp [hit_pos, add_nonneg]

private noncomputable def unitInterval : Measure ℝ := volume.restrict (Set.Icc 0 1)

private theorem integrable_hit (a b : ℝ) : Integrable (hit a b) unitInterval := by
  let : IsFiniteMeasure unitInterval := by unfold unitInterval; infer_instance
  exact (integrable_const (1 : ℝ)).indicator measurableSet_Icc

private theorem integral_hit (a b : ℝ) :
    ∫ θ, hit a b θ ∂unitInterval ≤ max (b-a) 0 := by
  unfold hit
  rw [show (fun _ : ℝ => (1 : ℝ)) = 1 from rfl, integral_indicator_one measurableSet_Icc]
  apply le_trans (b := volume.real (Set.Icc a b))
  · exact ENNReal.toReal_mono (measure_Icc_lt_top.ne) (Measure.restrict_le_self _)
  · exact Real.volume_real_Icc.le

private theorem width {u v : ℝ} (hu : |u| ≤ 1) (hv : |v| ≤ 1) (c : Bool) :
    (if c then 1 else 0 : ℝ) * max (1 - max |u| |v|) 0 +
      max (max u v - -(min u v)) 0 ≤
    (if c then (1+u)*(1+v) else 0) + |u+v| := by
  have hM := max_le hu hv
  have hp : |u*v| ≤ max |u| |v| := by
    rw [abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg _) hv).trans (le_max_left ..)
  have hs : max u v - -(min u v) = u+v := by grind
  rw [hs, max_eq_left (sub_nonneg.mpr hM)]
  cases c <;> simp only [Bool.false_eq_true, if_false, if_true, zero_mul, one_mul, zero_add]
  · exact max_le (le_abs_self _) (abs_nonneg _)
  · rcases le_total 0 (u+v) with h | h
    · rw [max_eq_left h, abs_of_nonneg h]; nlinarith [neg_abs_le (u*v)]
    · rw [max_eq_right h, abs_of_nonpos h]; nlinarith [neg_abs_le (u*v)]

theorem integrated_loss (u v : E → Literal V) (π : E → ℝ) (hπ : ∀ i, 0 ≤ π i)
    (z : V → ℝ) (t : V → Bool) (τ : ℝ)
    (far : ∀ s, τ ≤ ∑ i, π i * charge 1 s (u i) (v i)) :
    τ ≤ ∑ i, π i * (charge 1 t (u i) (v i) * max (1-max |score z (u i)| |score z (v i)|) 0 +
      max (max (score z (u i)) (score z (v i)) - -(min (score z (u i)) (score z (v i)))) 0) := by
  let A i := score z (u i)
  let B i := score z (v i)
  let m i := max |A i| |B i|
  let lo i := -(min (A i) (B i))
  let hi i := max (A i) (B i)
  let c i := charge 1 t (u i) (v i)
  let f i θ := π i * (c i * hit (m i) 1 θ + hit (lo i) (hi i) θ)
  have fi (i) : Integrable (f i) unitInterval :=
    (((integrable_hit ..).const_mul (c i)).add (integrable_hit ..)).const_mul (π i)
  let : IsFiniteMeasure unitInterval := by unfold unitInterval; infer_instance
  have h := setIntegral_mono_on (μ := (volume : Measure ℝ)) (s := Set.Icc 0 1)
    (f := fun _ => τ) (g := fun θ => ∑ i, f i θ)
    (show Integrable (fun _ => τ) unitInterval from integrable_const τ)
    (integrable_finsetSum univ (fun i _ => fi i)) measurableSet_Icc (fun θ hθ =>
      (far (choose z t θ)).trans (sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (clause_cover z t (u i) (v i) hθ) (hπ i)))
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h
  change _ ≤ ∫ θ, ∑ i, f i θ ∂unitInterval at h
  rw [integral_finsetSum univ (fun i _ => fi i)] at h
  simp only [sub_zero, smul_eq_mul, one_mul] at h
  apply h.trans (sum_le_sum (fun i _ => ?_))
  dsimp [f]
  rw [integral_const_mul, integral_add ((integrable_hit ..).const_mul _) (integrable_hit ..),
    integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (hπ i)
  have hc : 0 ≤ c i := by dsimp [c,charge]; split_ifs <;> norm_num
  exact add_le_add (mul_le_mul_of_nonneg_left (integral_hit (m i) 1) hc) (integral_hit (lo i) (hi i))

/-- A deterministic starting assignment, averaged over the uniform threshold. -/
theorem loss_bound (u v : E → Literal V) (π : E → ℝ) (hπ : ∀ i, 0 ≤ π i)
    (z : V → ℝ) (hz : ∀ x, |z x| ≤ 1) (t : V → Bool) (τ : ℝ)
    (far : ∀ s, τ ≤ ∑ i, π i * charge 1 s (u i) (v i)) :
    τ ≤ ∑ i, π i * (charge ((1+score z (u i))*(1+score z (v i))) t (u i) (v i) +
      |score z (u i) + score z (v i)|) := by
  apply (integrated_loss u v π hπ z t τ far).trans (sum_le_sum (fun i _ => ?_))
  apply mul_le_mul_of_nonneg_left _ (hπ i)
  have hz' (a : Literal V) : |score z a| ≤ 1 := by
    unfold score; split_ifs <;> simpa using hz a.var
  exact width (hz' (u i)) (hz' (v i)) ((u i).eval t && (v i).eval t)

theorem abs_average (π a : E → ℝ) (hπ : ∀ i, 0 ≤ π i) (h1 : ∑ i, π i = 1) :
    (∑ i, π i * |a i|) ≤ √(∑ i, π i * (a i)^2) := by
  have h := sum_mul_sq_le_sq_mul_sq univ (fun i => √(π i)) (fun i => √(π i)*|a i|)
  simp only [← mul_assoc, Real.mul_self_sqrt (hπ _), mul_pow, sq_abs, Real.sq_sqrt (hπ _),
    h1, one_mul] at h
  exact Real.le_sqrt_of_sq_le h

/-- Lemma 4.2, with an arbitrary finite distribution over starting assignments. -/
theorem reassignment_bound {A : Type*} [Fintype A] (u v : E → Literal V) (π : E → ℝ)
    (hπ : ∀ i, 0 ≤ π i) (h1 : ∑ i, π i = 1) (z : V → ℝ) (hz : ∀ x, |z x| ≤ 1)
    (t : A → V → Bool) (p : A → ℝ) (hp : ∀ s, 0 ≤ p s) (sp : ∑ s, p s = 1)
    {τ : ℝ} (hτ : τ ≤ 1) (far : ∀ s, τ ≤ ∑ i, π i * charge 1 s (u i) (v i))
    (hτ0 : 0 ≤ τ) :
    let D := ∑ i, π i * (score z (u i) + score z (v i))^2
    let U := ∑ s, p s * ∑ i, π i * charge ((1+score z (u i))*(1+score z (v i))) (t s) (u i) (v i)
    τ ≤ U + √D ∧ τ^2 ≤ D + 2*U := by
  dsimp only
  let D := ∑ i, π i * (score z (u i) + score z (v i))^2
  let U := ∑ s, p s * ∑ i, π i * charge ((1+score z (u i))*(1+score z (v i))) (t s) (u i) (v i)
  have av := sum_le_sum (s := univ) (fun s _ => mul_le_mul_of_nonneg_left
    (loss_bound u v π hπ z hz (t s) τ far) (hp s))
  simp only [mul_add,sum_add_distrib,← sum_mul,sp,one_mul] at av
  have factor (a b : ℝ) : (1+a)*1 + (1+a)*b = (1+a)*(1+b) := by ring
  simp only [factor] at av
  have hs : τ ≤ U + √D := av.trans (add_le_add_right (abs_average π (fun i => score z (u i)+score z (v i)) hπ h1) U)
  have hD : 0 ≤ D := sum_nonneg fun i _ => mul_nonneg (hπ i) (sq_nonneg _)
  have hU : 0 ≤ U := by
    apply sum_nonneg; intro s _
    apply mul_nonneg (hp s) (sum_nonneg _)
    intro i _
    apply mul_nonneg (hπ i)
    have hz' (a : Literal V) : 0 ≤ 1+score z a := by
      unfold score; split_ifs <;> linarith [(abs_le.mp (hz a.var)).1,(abs_le.mp (hz a.var)).2]
    unfold charge
    split_ifs <;> first | exact mul_nonneg (hz' _) (hz' _) | rfl
  refine ⟨hs, ?_⟩
  change τ^2 ≤ D + 2*U
  by_cases h : U ≤ τ
  · have hh := pow_le_pow_left₀ (sub_nonneg.mpr h) (show τ-U ≤ √D by linarith) 2
    rw [Real.sq_sqrt hD] at hh
    nlinarith only [hh, mul_le_mul_of_nonneg_right hτ hU, sq_nonneg U]
  · nlinarith only [mul_le_mul_of_nonneg_left hτ hτ0,hD,hU,le_of_not_ge h]

end TwoSAT.Reassignment

end

section

namespace TwoSAT.Entropy

open Finset
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

/-- Relative entropy for finite masses, used with the explicit support
condition that positive numerator mass implies positive denominator mass. -/
noncomputable def divergence (q p : Ω → ℝ) : ℝ :=
  ∑ i, q i * Real.log (q i / p i)

noncomputable def removed (q p : Ω → ℝ) (L : ℝ) (i : Ω) : ℝ :=
  if Real.exp L * p i < q i then q i else 0

noncomputable def kept (q p : Ω → ℝ) (L : ℝ) (i : Ω) : ℝ :=
  if Real.exp L * p i < q i then 0 else q i

private theorem negPart {q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p) (support : 0 < q → 0 < p) :
    0 ≤ q * Real.log (q / p) + p := by
  rcases hq.eq_or_lt with h | h
  · simp [← h, hp]
  have hp' := support h
  have hh := Real.one_sub_inv_le_log_of_pos (div_pos h hp')
  have hh' := mul_le_mul_of_nonneg_left hh h.le
  have hcancel : q * (q / p)⁻¹ = p := by field_simp
  rw [mul_sub, mul_one, hcancel] at hh'
  linarith

/-- The entropy tail estimate used to truncate each joint distribution in §6.1. -/
theorem mass_removed {q p : Ω → ℝ} {L d : ℝ} (hL : 0 < L)
    (hq : ∀ i, 0 ≤ q i) (hp : ∀ i, 0 ≤ p i) (support : ∀ i, 0 < q i → 0 < p i)
    (hs : ∑ i, p i = 1) (hd : divergence q p ≤ d) :
    ∑ i, removed q p L i ≤ (d + 1) / L := by
  apply (le_div_iff₀ hL).mpr
  rw [sum_mul]
  calc
    _ ≤ ∑ i, (q i * Real.log (q i / p i) + p i) := by
      apply sum_le_sum
      intro i _
      unfold removed
      split_ifs with hb
      · have hqi := lt_of_le_of_lt (mul_nonneg (Real.exp_pos L).le (hp i)) hb
        have hpi := support i hqi
        have he : Real.exp L < q i / p i := (lt_div_iff₀ hpi).mpr hb
        have hl := Real.log_lt_log (Real.exp_pos L) he
        rw [Real.log_exp] at hl
        nlinarith [mul_le_mul_of_nonneg_left hl.le (hq i), hp i]
      · simpa using negPart (hq i) (hp i) (support i)
    _ ≤ d + 1 := by simpa [sum_add_distrib, hs, divergence] using add_le_add_right hd 1

noncomputable def affinity (q p : Ω → ℝ) : ℝ := ∑ i, √(q i) * √(p i)

theorem affinity_le (q p : Ω → ℝ) (hq : ∀ i, 0 ≤ q i) (hp : ∀ i, 0 ≤ p i) :
    affinity q p ≤ √(∑ i, q i) * √(∑ i, p i) :=
  Real.sum_sqrt_mul_sqrt_le univ hq hp

omit [Fintype Ω] in
private theorem sqrt_split (q p : Ω → ℝ) (L : ℝ) (i : Ω) :
    √(q i) = √(removed q p L i) + √(kept q p L i) := by
  simp only [removed, kept]; split_ifs <;> simp

/-- Discarding mass δ from a distribution decreases its affinity with its
complement by at most 2√δ. The permutation can also act on joint outcomes. -/
theorem truncate_affinity (e : Ω ≃ Ω) (q p : Ω → ℝ) (L : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hs : ∑ i, q i = 1) :
    affinity q (q ∘ e) ≤ affinity (kept q p L) (kept q p L ∘ e) +
      2 * √(∑ i, removed q p L i) := by
  let r := removed q p L
  let k := kept q p L
  have hr (i) : 0 ≤ r i := by dsimp [r, removed]; split_ifs <;> simp [hq]
  have hk (i) : 0 ≤ k i := by dsimp [k, kept]; split_ifs <;> simp [hq]
  have hkle (i) : k i ≤ q i := by dsimp [k, kept]; split_ifs <;> simp [hq]
  have hk1 : ∑ i, k i ≤ 1 := (sum_le_sum (fun i _ => hkle i)).trans hs.le
  have hq' : ∑ i, q (e i) = 1 := (e.sum_comp q).trans hs
  have hr' : ∑ i, r (e i) = ∑ i, r i := e.sum_comp r
  have h1 := affinity_le r (q ∘ e) hr (fun i => hq (e i))
  have h2 := affinity_le k (r ∘ e) hk (fun i => hr (e i))
  simp only [Function.comp_apply, hq', Real.sqrt_one, mul_one] at h1
  simp only [Function.comp_apply, hr'] at h2
  have hk' : √(∑ i, k i) ≤ 1 := by simpa using Real.sqrt_le_sqrt hk1
  have h2' := h2.trans (mul_le_mul_of_nonneg_right hk' (Real.sqrt_nonneg _))
  rw [one_mul] at h2'
  have hsplit : affinity q (q ∘ e) = affinity k (k ∘ e) + affinity r (q ∘ e) +
      affinity k (r ∘ e) := by
    simp only [affinity, Function.comp_apply, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    have ha : √(q i) = √(r i) + √(k i) := sqrt_split q p L _
    have hb : √(q (e i)) = √(r (e i)) + √(k (e i)) := sqrt_split q p L _
    rw [ha, hb]; ring
  change affinity q (q ∘ e) ≤ affinity k (k ∘ e) + 2 * √(∑ i, r i)
  linarith

variable {S Z : Type*} [Fintype S] [Fintype Z]

/-- Unnormalized contribution from one seed. Summing over the seeds already
accounts for their probabilities in the joint mass. -/
noncomputable def row (e : Z ≃ Z) (q : S × Z → ℝ) (s : S) : ℝ :=
  affinity (fun z => q (s, z)) (fun z => q (s, e z))

noncomputable def twoWay (e : Z ≃ Z) (q₀ q₁ : S × Z → ℝ) : ℝ :=
  ∑ s, min (row e q₀ s) (row e q₁ s)

private theorem sum_rows (e : Z ≃ Z) (q : S × Z → ℝ) :
    ∑ s, row e q s = affinity q (q ∘ (Equiv.prodCongr (Equiv.refl S) e)) := by
  simp [row, affinity, Fintype.sum_prod_type]

omit [Fintype S] in
private theorem row_mono (e : Z ≃ Z) {p q : S × Z → ℝ}
    (h : ∀ i, p i ≤ q i) (s : S) : row e p s ≤ row e q s := by
  unfold row affinity
  apply sum_le_sum
  intro z _
  exact mul_le_mul (Real.sqrt_le_sqrt (h _)) (Real.sqrt_le_sqrt (h _))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

omit [Fintype S] in
private theorem row_scale (e : Z ≃ Z) {c : ℝ} (hc : 0 ≤ c) (p : S × Z → ℝ) (s : S) :
    row e (fun i => c * p i) s = c * row e p s := by
  simp only [row, affinity, mul_sum, Real.sqrt_mul hc]
  apply sum_congr rfl
  intro z _
  nlinarith only [Real.sq_sqrt hc,
    congrArg (fun a => a * (√(p (s, z)) * √(p (s, e z)))) (Real.sq_sqrt hc)]

private theorem row_error (e : Z ≃ Z) {q p : S × Z → ℝ} {L d : ℝ}
    (hL : 0 < L) (hq : ∀ i, 0 ≤ q i) (hp : ∀ i, 0 ≤ p i)
    (support : ∀ i, 0 < q i → 0 < p i) (hsq : ∑ i, q i = 1)
    (hsp : ∑ i, p i = 1) (hd : divergence q p ≤ d) :
    ∑ s, (row e q s - row e (kept q p L) s) ≤ 2 * √((d + 1) / L) := by
  have ht := truncate_affinity (Equiv.prodCongr (Equiv.refl S) e) q p L hq hsq
  have hw := Real.sqrt_le_sqrt (mass_removed hL hq hp support hsp hd)
  rw [sum_sub_distrib, sum_rows, sum_rows]
  linarith

omit [Fintype S] in
private theorem row_partial (e : Z ≃ Z) (q p : S × Z → ℝ) (L : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hp : ∀ i, 0 ≤ p i) (s : S) :
    row e (kept q p L) s ≤ row e q s ∧ row e (kept q p L) s ≤ Real.exp L * row e p s := by
  constructor
  · apply row_mono
    intro i
    unfold kept
    split_ifs <;> simp [hq]
  · rw [← row_scale e (Real.exp_pos L).le]
    apply row_mono
    intro i
    unfold kept
    split_ifs with h
    · exact mul_nonneg (Real.exp_pos L).le (hp i)
    · exact le_of_not_gt h

/-- Lemma 6.2 for the two pairs of joint seed and endpoint distributions.
The min is taken at each seed before summing, as required for two-way walks. -/
theorem compare_twoWay (e : Z ≃ Z) (q p : Bool → S × Z → ℝ) {b d : ℝ}
    (hb : 0 < b) (hd : 0 ≤ d) (hq : ∀ j i, 0 ≤ q j i) (hp : ∀ j i, 0 ≤ p j i)
    (sq : ∀ j, ∑ i, q j i = 1) (sp : ∀ j, ∑ i, p j i = 1)
    (supp : ∀ j i, 0 < q j i → 0 < p j i) (kl : ∀ j, divergence (q j) (p j) ≤ d)
    (hB : b ≤ twoWay e (q false) (q true)) :
    b / 2 * Real.exp (-(64 * (d + 1) / b ^ 2)) ≤ twoWay e (p false) (p true) := by
  let L := 64 * (d + 1) / b ^ 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hsqrt : √((d + 1) / L) = b / 8 := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).mpr
    dsimp [L]; field_simp; ring
  let k (j : Bool) := kept (q j) (p j) L
  have herr (j : Bool) := row_error e hL (hq j) (hp j) (supp j) (sq j) (sp j) (kl j)
  have herr' (j : Bool) : ∑ s, (row e (q j) s - row e (k j) s) ≤ b / 4 := by
    have h := herr j
    rw [hsqrt] at h
    change _ ≤ b / 4
    linarith
  have hrows (j : Bool) := row_partial e (q j) (p j) L (hq j) (hp j)
  have hsum : twoWay e (q false) (q true) ≤ Real.exp L * twoWay e (p false) (p true) +
      (∑ s, (row e (q false) s - row e (k false) s)) +
      ∑ s, (row e (q true) s - row e (k true) s) := by
    unfold twoWay
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro s _
    have hf := hrows false s
    have ht := hrows true s
    change row e (k false) s ≤ _ ∧ row e (k false) s ≤ _ at hf
    change row e (k true) s ≤ _ ∧ row e (k true) s ≤ _ at ht
    rcases le_total (row e (p false) s) (row e (p true) s) with h | h
    · rw [min_eq_left h]
      linarith [min_le_left (row e (q false) s) (row e (q true) s)]
    · rw [min_eq_right h]
      linarith [min_le_right (row e (q false) s) (row e (q true) s)]
  change b / 2 * Real.exp (-L) ≤ _
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos L)]
  linarith [herr' true, herr' false, mul_comm (Real.exp L) (twoWay e (p false) (p true))]

end TwoSAT.Entropy

end

section

namespace TwoSAT.ColumnRounding

open Finset TwoSAT.Weights TwoSAT.Entropy

variable {V E S : Type} [Fintype V] [Fintype E] [Fintype S]

omit [Fintype V] in
private theorem coordinate (u v : E → Literal V) (w : E → ℝ) (hw : ∀ i, 0 ≤ w i)
    (t : V → Bool) (best : ∀ t', (∑ i, w i * charge 1 t (u i) (v i)) ≤
      ∑ i, w i * charge 1 t' (u i) (v i))
    (q : Literal V → ℝ) (anti : ∀ a, q a.flip = -q a) (unit : ∀ a, |q a| ≤ 1) :
    (∑ i, (w i * charge 1 t (u i) (v i)) * |q (u i)|) ≤ ∑ i, w i * |q (u i)+q (v i)| := by
  let z (x : V) := q ⟨x,true⟩
  have hq (a : Literal V) : score z a = q a := by
    rcases a with ⟨x,b⟩; cases b
    · exact (anti ⟨x,true⟩).symm
    · rfl
  have h := TwoSAT.Reassignment.integrated_loss u v w hw z t _ best
  simp only [hq] at h
  have one (i : E) : w i * (charge 1 t (u i) (v i) *
      max (1-max |q (u i)| |q (v i)|) 0 +
      max (max (q (u i)) (q (v i)) - -(min (q (u i)) (q (v i)))) 0) ≤
      w i * charge 1 t (u i) (v i) - w i * charge 1 t (u i) (v i) * |q (u i)| +
        w i * |q (u i)+q (v i)| := by
    have hc : 0 ≤ charge 1 t (u i) (v i) := by unfold charge; split_ifs <;> norm_num
    have hmax : max (q (u i)) (q (v i)) - -(min (q (u i)) (q (v i))) = q (u i)+q (v i) := by grind
    rw [hmax]
    have h1 : max (1-max |q (u i)| |q (v i)|) 0 ≤ 1-|q (u i)| := by grind [unit (u i)]
    have h2 := add_le_add (mul_le_mul_of_nonneg_left h1 hc)
      (max_le (le_abs_self (q (u i)+q (v i))) (abs_nonneg _))
    exact (mul_le_mul_of_nonneg_left h2 (hw i)).trans_eq (by ring)
  have hh := h.trans (sum_le_sum (s := univ) (fun i _ => one i))
  rw [sum_add_distrib,sum_sub_distrib] at hh
  linarith only [hh]

private theorem separation (p r : S → ℝ) (hp : ∀ s, 0 ≤ p s) (hr : ∀ s, 0 ≤ r s)
    (sp : ∑ s, p s = 1) (sr : ∑ s, r s = 1) :
    2 ≤ (∑ s, |p s-r s|) + 2*affinity p r := by
  have pt (s : S) : p s + r s ≤ |p s-r s| + 2*(√(p s)*√(r s)) := by
    rcases le_total (p s) (r s) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      nlinarith only [Real.mul_self_sqrt (hp s),mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg (p s))]
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      nlinarith only [Real.mul_self_sqrt (hr s),mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg (r s))]
  have h := sum_le_sum (s := univ) (fun s _ => pt s)
  simp only [sum_add_distrib,sp,sr,← mul_sum] at h
  unfold affinity; linarith only [h]

/-- Round the endpoint columns using a minimum-loss assignment and one coordinate threshold.
The two terms are the complementary-column affinity and the change along implications. -/
theorem round_columns (u v : E → Literal V) (w : E → ℝ) (hw : ∀ i, 0 ≤ w i)
    (p : Literal V → S → ℝ) (hp : ∀ l s, 0 ≤ p l s) (sp : ∀ l, ∑ s, p l s = 1)
    {δ : ℝ} (far : ∀ t, δ ≤ ∑ i, w i * charge 1 t (u i) (v i)) :
    2*δ ≤ ∑ i, w i * (2*affinity (p (u i)) (p (u i).flip) +
      ∑ s, (|p (u i) s-p (v i).flip s| + |p (v i) s-p (u i).flip s|)) := by
  classical
  let L (t : V → Bool) := ∑ i, w i * charge 1 t (u i) (v i)
  obtain ⟨t,_,hm⟩ := univ.exists_min_image L univ_nonempty
  let c i := charge 1 t (u i) (v i)
  let q (s : S) (l : Literal V) := p l s - p l.flip s
  have anti (s : S) (l : Literal V) : q s l.flip = -q s l := by simp [q]
  have le1 (l : Literal V) (s : S) : p l s ≤ 1 := by
    rw [← sp l]; exact single_le_sum (fun j _ => hp l j) (mem_univ _)
  have unit (s : S) (l : Literal V) : |q s l| ≤ 1 := by
    dsimp [q]; rw [abs_le]; constructor <;> linarith [hp l s,hp l.flip s,le1 l s,le1 l.flip s]
  have row (s : S) := coordinate u v w hw t (fun t' => hm t' (mem_univ _)) (q s) (anti s) (unit s)
  have hh := sum_le_sum (s := univ) (fun s _ => row s)
  rw [sum_comm,Finset.sum_comm (f := fun s i => w i * |q s (u i)+q s (v i)|)] at hh
  simp only [← mul_sum] at hh
  let a i := affinity (p (u i)) (p (u i).flip)
  have pt (i : E) : 2*(w i*c i) ≤ w i * (2*a i) + (w i*c i)* ∑ s, |q s (u i)| := by
    have sep := separation _ _ (hp (u i)) (hp (u i).flip) (sp _) (sp _)
    have hc : 0 ≤ a i := sum_nonneg fun j _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    dsimp [c,charge]; split_ifs
    · simp only [mul_one]; dsimp [a,q]; linarith only [mul_le_mul_of_nonneg_left sep (hw i)]
    · simpa only [mul_zero,zero_mul,add_zero] using mul_nonneg (hw i) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hc)
  have tri (s : S) (i : E) : |q s (u i)+q s (v i)| ≤
      |p (u i) s-p (v i).flip s| + |p (v i) s-p (u i).flip s| := by
    rw [show q s (u i)+q s (v i) = (p (u i) s-p (v i).flip s)+(p (v i) s-p (u i).flip s) by dsimp [q]; ring]
    exact abs_add_le .. 
  have hh' := hh.trans (sum_le_sum (s := univ) (fun i _ => mul_le_mul_of_nonneg_left
    (sum_le_sum (s := univ) (fun s _ => tri s i)) (hw i)))
  have h := sum_le_sum (s := univ) (fun i _ => pt i)
  rw [← mul_sum,sum_add_distrib] at h
  conv_rhs => enter [2,i]; rw [mul_add]
  rw [sum_add_distrib]
  exact (mul_le_mul_of_nonneg_left (far t) (by norm_num : (0:ℝ) ≤ 2)).trans
    (h.trans (add_le_add_right hh' _))

end TwoSAT.ColumnRounding

end

section

namespace TwoSAT.Walk

open Finset
open scoped BigOperators

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Probability of a transition from the row index to the column index. -/
structure Kernel (S : Type*) [Fintype S] where
  prob : S → S → ℝ
  nonneg : ∀ s t, 0 ≤ prob s t
  row : ∀ s, ∑ t, prob s t = 1

namespace Kernel

variable (K : Kernel S)

noncomputable def steps : ℕ → S → S → ℝ
  | 0, s, t => if s = t then 1 else 0
  | r+1, s, t => ∑ u, K.prob s u * steps r u t

theorem steps_nonneg (r : ℕ) (s t : S) : 0 ≤ K.steps r s t := by
  induction r generalizing s with
  | zero => simp only [steps]; split_ifs <;> norm_num
  | succ r ih => exact sum_nonneg fun u _ => mul_nonneg (K.nonneg s u) (ih u)

theorem steps_row (r : ℕ) (s : S) : ∑ t, K.steps r s t = 1 := by
  induction r generalizing s with
  | zero => simp [steps]
  | succ r ih =>
    simp only [steps]
    rw [sum_comm]
    simp only [← mul_sum, ih, mul_one, K.row]

theorem steps_le_one (r : ℕ) (s t : S) : K.steps r s t ≤ 1 := by
  rw [← K.steps_row r s]
  exact single_le_sum (fun u _ => K.steps_nonneg r s u) (mem_univ t)

noncomputable def endpoint (η : ℝ) (s t : S) :=
  η * ∑' r : ℕ, (1-η)^r * K.steps r s t

theorem summable_steps {η : ℝ} (hη : 0 < η) (hu : η < 1) (s t : S) :
    Summable (fun r : ℕ => (1-η)^r * K.steps r s t) := by
  apply Summable.of_nonneg_of_le (fun r => mul_nonneg (pow_nonneg (by linarith) _) (K.steps_nonneg r s t))
    (fun r => mul_le_of_le_one_right (pow_nonneg (by linarith) _) (K.steps_le_one r s t))
    (summable_geometric_of_lt_one (by linarith) (by linarith))

theorem endpoint_nonneg {η : ℝ} (hη : 0 < η) (hu : η < 1) (s t : S) : 0 ≤ K.endpoint η s t :=
  mul_nonneg hη.le (tsum_nonneg (fun r => mul_nonneg (pow_nonneg (by linarith) _) (K.steps_nonneg r s t)))

theorem endpoint_row {η : ℝ} (hη : 0 < η) (hu : η < 1) (s : S) : ∑ t, K.endpoint η s t = 1 := by
  simp only [endpoint, ← mul_sum]
  rw [← Summable.tsum_finsetSum (fun t (_ : t ∈ univ) => K.summable_steps hη hu s t)]
  simp only [← mul_sum, K.steps_row, mul_one]
  rw [tsum_geometric_of_lt_one (by linarith) (by linarith)]
  rw [show 1-(1-η) = η by ring, mul_inv_cancel₀ hη.ne']

noncomputable def geometric (η : ℝ) (hη : 0 < η) (hu : η < 1) : Kernel S :=
  ⟨K.endpoint η, K.endpoint_nonneg hη hu, K.endpoint_row hη hu⟩

/-- Conditioning on the first stopping decision gives equation (23). -/
theorem endpoint_rec {η : ℝ} (hη : 0 < η) (hu : η < 1) (s t : S) :
    K.endpoint η s t = η * (if s = t then 1 else 0) +
      (1-η) * ∑ u, K.prob s u * K.endpoint η u t := by
  have expand (r : ℕ) : (1-η)^(r+1) * K.steps (r+1) s t =
      ∑ u, ((1-η) * K.prob s u) * ((1-η)^r * K.steps r u t) := by
    simp only [steps, pow_succ, mul_sum]
    apply sum_congr rfl
    intros; ring
  rw [endpoint, (K.summable_steps hη hu s t).tsum_eq_zero_add]
  simp only [pow_zero, one_mul, show K.steps 0 s t = (if s = t then 1 else 0) from rfl]
  simp_rw [expand]
  rw [Summable.tsum_finsetSum (fun u (_ : u ∈ univ) =>
    (K.summable_steps hη hu u t).mul_left ((1-η)*K.prob s u))]
  simp only [tsum_mul_left, endpoint, mul_add, mul_sum]
  congr 1
  apply sum_congr rfl
  intros; ring

def Stationary (μ : S → ℝ) := ∀ t, ∑ s, μ s * K.prob s t = μ t

theorem endpoint_stationary {μ : S → ℝ} (stat : K.Stationary μ) {η : ℝ}
    (hη : 0 < η) (hu : η < 1) : (K.geometric η hη hu).Stationary μ := by
  intro t
  have stationary (j : S) := stat j
  let A := ∑ s, μ s * K.endpoint η s t
  have h : A = η * μ t + (1-η) * A := by
    change (∑ s, μ s * K.endpoint η s t) = _
    conv_lhs => enter [2, s, 2]; rw [K.endpoint_rec hη hu]
    simp only [mul_add, sum_add_distrib]
    congr 1
    · simp [mul_ite, mul_comm]
    · have reorder (s : S) : μ s * ((1-η) * ∑ u, K.prob s u * K.endpoint η u t) =
          (1-η) * ∑ u, (μ s * K.prob s u) * K.endpoint η u t := by
        rw [mul_left_comm, mul_sum]
        simp only [mul_assoc]
      simp_rw [reorder]
      rw [← mul_sum, sum_comm]
      simp only [← sum_mul, stationary, A]
  change A = μ t
  have hz : η * (A - μ t) = 0 := by linarith only [h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hη.ne')

end Kernel
end TwoSAT.Walk

end

section

namespace TwoSAT.Entropy

open Finset

noncomputable def rel (a b : ℝ) := a * Real.log (a/b)

/-- Tangent-plane bound for relative entropy, including a zero source mass. -/
private theorem tangent {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 < r)
    (supp : 0 < a → 0 < b) : a * Real.log r + a - b*r ≤ rel a b := by
  rcases ha.eq_or_lt with h | h
  · subst a; simpa [rel] using mul_nonneg hb hr.le
  have hbp := supp h
  have hp := div_pos h (mul_pos hbp hr)
  have hl := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hp) h.le
  have hi : a * (a/(b*r))⁻¹ = b*r := by field_simp
  rw [mul_sub, mul_one, hi] at hl
  rw [Real.log_div h.ne' (mul_pos hbp hr).ne', Real.log_mul hbp.ne' hr.ne'] at hl
  rw [rel, Real.log_div h.ne' hbp.ne']
  linarith only [hl]

theorem log_sum {I : Type*} [Fintype I] (a b : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i) (supp : ∀ i, 0 < a i → 0 < b i) :
    rel (∑ i, a i) (∑ i, b i) ≤ ∑ i, rel (a i) (b i) := by
  let A := ∑ i, a i
  let B := ∑ i, b i
  have hA : 0 ≤ A := sum_nonneg fun i _ => ha i
  rcases hA.eq_or_lt with hz | hA
  · have h0 (i : I) : a i = 0 := le_antisymm
        ((single_le_sum (fun j _ => ha j) (mem_univ i)).trans hz.ge) (ha i)
    simp [h0, rel]
  have hB : 0 < B := by
    obtain ⟨i,_,hi⟩ := (sum_pos_iff_of_nonneg (fun i _ => ha i)).mp hA
    exact (supp _ hi).trans_le (single_le_sum (fun j _ => hb j) (mem_univ i))
  have h := sum_le_sum (s := univ) (fun i _ => tangent (ha i) (hb i) (div_pos hA hB) (supp i))
  simp only [sum_sub_distrib, sum_add_distrib, ← sum_mul] at h
  change A * Real.log (A/B) + A - B*(A/B) ≤ _ at h
  have he : B*(A/B) = A := by field_simp
  simpa only [he, add_sub_cancel_right, rel, A, B] using h

theorem rel_add_le {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (sa : 0 < a → 0 < b) (sx : 0 < x → 0 < y) :
    rel (a+x) (b+y) ≤ rel a b + rel x y := by
  let f (i : Bool) := if i then a else x
  let g (i : Bool) := if i then b else y
  have h := log_sum f g (fun i => by cases i <;> simp_all [f])
    (fun i => by cases i <;> simp_all [g]) (fun i => by cases i <;> simp_all [f,g])
  simpa [Fintype.sum_bool, f,g,add_comm] using h

theorem rel_product {a b x y : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x)
    (sab : 0 < a → 0 < b) (sxy : 0 < x → 0 < y) :
    rel (a*x) (b*y) = x * rel a b + a * rel x y := by
  rcases ha.eq_or_lt with h | h
  · simp [← h, rel]
  rcases hx.eq_or_lt with h' | h'
  · simp [← h', rel]
  rw [rel, mul_div_mul_comm, Real.log_mul (div_pos h (sab h)).ne' (div_pos h' (sxy h')).ne']
  unfold rel
  ring

theorem rel_scale {a b w : ℝ} (hw : 0 ≤ w) (ha : 0 ≤ a) (s : 0 < a → 0 < b) :
    rel (w*a) (w*b) = w * rel a b := by
  rw [rel_product hw ha id s]
  simp [rel]

variable {I J : Type*} [Fintype I] [Fintype J]

theorem joint_chain (a b : I → ℝ) (k l : I → J → ℝ)
    (ha : ∀ i, 0 ≤ a i) (sa : ∀ i, 0 < a i → 0 < b i)
    (hk : ∀ i j, 0 ≤ k i j) (sk : ∀ i j, 0 < k i j → 0 < l i j)
    (row : ∀ i, ∑ j, k i j = 1) :
    divergence (fun x : I × J => a x.1 * k x.1 x.2) (fun x => b x.1 * l x.1 x.2) =
      divergence a b + ∑ i, a i * divergence (k i) (l i) := by
  change (∑ x : I × J, rel _ _) = _
  rw [Fintype.sum_prod_type]
  have hp (i : I) (j : J) := rel_product (ha i) (hk i j) (sa i) (sk i j)
  simp only [hp, sum_add_distrib, ← sum_mul, ← mul_sum, row, one_mul]
  rfl

/-- Forgetting the intermediate state cannot increase divergence. -/
theorem mix_bound (a b : I → ℝ) (k l : I → J → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (sa : ∀ i, 0 < a i → 0 < b i)
    (hk : ∀ i j, 0 ≤ k i j) (hl : ∀ i j, 0 ≤ l i j)
    (sk : ∀ i j, 0 < k i j → 0 < l i j) (row : ∀ i, ∑ j, k i j = 1) :
    divergence (fun j => ∑ i, a i * k i j) (fun j => ∑ i, b i * l i j) ≤
      divergence a b + ∑ i, a i * divergence (k i) (l i) := by
  rw [← joint_chain a b k l ha sa hk sk row]
  change (∑ j, rel _ _) ≤ ∑ x : I × J, rel _ _
  rw [Fintype.sum_prod_type, sum_comm]
  apply sum_le_sum
  intro j _
  exact log_sum _ _ (fun i => mul_nonneg (ha i) (hk i j)) (fun i => mul_nonneg (hb i) (hl i j))
    (fun i hp => mul_pos (sa i (pos_of_mul_pos_left hp (hk i j)))
      (sk i j (pos_of_mul_pos_right hp (ha i))))

end TwoSAT.Entropy

end

section

namespace TwoSAT.Walk

open Finset TwoSAT.Entropy
open scoped BigOperators

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem mix_identity {I : Type*} [Fintype I] (h : I → ℝ) (p q : I → ℝ)
    (hh : ∀ i, 0 ≤ h i) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (sup : ∀ i, 0 < p i → 0 < q i) {a : ℝ} (ha : 0 ≤ a) :
    divergence (fun i => h i + a*p i) (fun i => h i + a*q i) ≤ a * divergence p q := by
  rw [divergence, divergence, mul_sum]
  apply sum_le_sum
  intro i _
  have hs (hpos : 0 < a*p i) : 0 < a*q i :=
    mul_pos (pos_of_mul_pos_left hpos (hp i)) (sup i (pos_of_mul_pos_right hpos ha))
  have hle := rel_add_le (hh i) (hh i) (mul_nonneg ha (hp i)) (mul_nonneg ha (hq i)) id hs
  rw [rel_scale ha (hp i) (sup i)] at hle
  simpa [rel] using hle

namespace Kernel

def Supports (Q P : Kernel S) := ∀ s t, 0 < Q.prob s t → 0 < P.prob s t

theorem steps_support {Q P : Kernel S} (h : Q.Supports P) (r : ℕ) (s t : S) :
    0 < Q.steps r s t → 0 < P.steps r s t := by
  induction r generalizing s with
  | zero => exact id
  | succ r ih =>
    intro hpos
    obtain ⟨i, _, hi⟩ := (sum_pos_iff_of_nonneg (fun i _ =>
      mul_nonneg (Q.nonneg s i) (Q.steps_nonneg r i t))).mp hpos
    apply lt_of_lt_of_le _ (single_le_sum (fun i _ =>
      mul_nonneg (P.nonneg s i) (P.steps_nonneg r i t)) (mem_univ i))
    exact mul_pos (h _ _ (pos_of_mul_pos_left hi (Q.steps_nonneg r i t)))
      (ih _ (pos_of_mul_pos_right hi (Q.nonneg s i)))

theorem geometric_support {Q P : Kernel S} (h : Q.Supports P) {η : ℝ} (hη : 0 < η)
    (hu : η < 1) : (Q.geometric η hη hu).Supports (P.geometric η hη hu) := by
  intro s t hp
  change 0 < Q.endpoint η s t at hp
  change 0 < P.endpoint η s t
  have hex : ∃ r, 0 < Q.steps r s t := by
    by_contra! none
    have hz (r : ℕ) := (none r).antisymm (Q.steps_nonneg r s t)
    simp [endpoint, hz] at hp
  obtain ⟨r, hr⟩ := hex
  apply mul_pos hη
  apply (P.summable_steps hη hu s t).tsum_pos (fun j =>
    mul_nonneg (pow_nonneg (by linarith) _) (P.steps_nonneg j s t)) r
  exact mul_pos (pow_pos (by linarith) _) (steps_support h r s t hr)

/-- For a geometric stopping time, the expected conditional endpoint divergence is at
most the expected number of steps times the one-step divergence at stationarity. -/
theorem stopped_divergence (Q P : Kernel S) (sup : Q.Supports P) (μ : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (stat : Q.Stationary μ) {η : ℝ} (hη : 0 < η) (hu : η < 1) :
    (∑ s, μ s * divergence (Q.endpoint η s) (P.endpoint η s)) ≤
      ((1-η)/η) * ∑ s, μ s * divergence (Q.prob s) (P.prob s) := by
  let H s := divergence (Q.endpoint η s) (P.endpoint η s)
  let D s := divergence (Q.prob s) (P.prob s)
  have gs := geometric_support sup hη hu
  have recurse (s : S) : H s ≤ (1-η) * (D s + ∑ i, Q.prob s i * H i) := by
    let q (j : S) := ∑ i, Q.prob s i * Q.endpoint η i j
    let p (j : S) := ∑ i, P.prob s i * P.endpoint η i j
    have qpos (j : S) : 0 ≤ q j := sum_nonneg fun i _ => mul_nonneg (Q.nonneg ..) (Q.endpoint_nonneg hη hu ..)
    have ppos (j : S) : 0 ≤ p j := sum_nonneg fun i _ => mul_nonneg (P.nonneg ..) (P.endpoint_nonneg hη hu ..)
    have sqp (j : S) (hj : 0 < q j) : 0 < p j := by
      obtain ⟨i, _, hi⟩ := (sum_pos_iff_of_nonneg (fun i _ =>
        mul_nonneg (Q.nonneg s i) (Q.endpoint_nonneg hη hu i j))).mp hj
      exact (mul_pos (sup s i (pos_of_mul_pos_left hi (Q.endpoint_nonneg hη hu i j)))
        (gs i j (pos_of_mul_pos_right hi (Q.nonneg s i)))).trans_le
        (single_le_sum (fun i _ => mul_nonneg (P.nonneg s i) (P.endpoint_nonneg hη hu i j)) (mem_univ i))
    have step := mix_bound (Q.prob s) (P.prob s) (Q.endpoint η) (P.endpoint η)
      (Q.nonneg s) (P.nonneg s) (sup s) (Q.endpoint_nonneg hη hu) (P.endpoint_nonneg hη hu)
      gs (Q.endpoint_row hη hu)
    apply le_trans _ (mul_le_mul_of_nonneg_left step (sub_nonneg.mpr hu.le))
    have stop (j : S) : 0 ≤ η * (if s = j then (1 : ℝ) else 0) := by split_ifs <;> simp [hη.le]
    have hh := mix_identity _ q p stop qpos ppos sqp (sub_nonneg.mpr hu.le)
    have qrec : Q.endpoint η s = fun j => η*(if s=j then 1 else 0)+(1-η)*q j :=
      funext (Q.endpoint_rec hη hu s)
    have prec : P.endpoint η s = fun j => η*(if s=j then 1 else 0)+(1-η)*p j :=
      funext (P.endpoint_rec hη hu s)
    unfold H
    rw [qrec, prec]
    exact hh
  have stationary (i : S) := stat i
  have st : ∑ s, μ s * (∑ i, Q.prob s i * H i) = ∑ i, μ i * H i := by
    simp only [mul_sum, ← mul_assoc]
    rw [sum_comm]; simp only [← sum_mul, stationary]
  have h := sum_le_sum (s := univ) (fun s _ => mul_le_mul_of_nonneg_left (recurse s) (hμ s))
  simp_rw [mul_left_comm (μ _) (1-η), ← mul_sum, mul_add, sum_add_distrib, st] at h
  change (∑ s, μ s * H s) ≤ _ * ∑ s, μ s * D s
  rw [div_mul_eq_mul_div, le_div_iff₀ hη]
  linarith only [h]

/-- Keeping the seed and reporting the (optionally relabeled) endpoint adds only the
initial divergence. A complementary start is allowed when it preserves the seed law. -/
theorem joint_endpoint_bound (Q P : Kernel S) (sup : Q.Supports P) (μ ν : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (sm : ∀ s, 0 < μ s → 0 < ν s) (stat : Q.Stationary μ)
    (start report : S ≃ S) (preserve : ∀ s, μ (start s) = μ s) {η : ℝ}
    (hη : 0 < η) (hu : η < 1) :
    divergence (fun a : S × S => μ a.1 * Q.endpoint η (start a.1) (report a.2))
      (fun a => ν a.1 * P.endpoint η (start a.1) (report a.2)) ≤
      divergence μ ν + ((1-η)/η) * ∑ s, μ s * divergence (Q.prob s) (P.prob s) := by
  have gs := geometric_support sup hη hu
  rw [joint_chain μ ν (fun s j => Q.endpoint η (start s) (report j))
    (fun s j => P.endpoint η (start s) (report j)) hμ sm
    (fun s j => Q.endpoint_nonneg hη hu (start s) (report j)) (fun s j => gs (start s) (report j))
    (fun s => (report.sum_comp (Q.endpoint η (start s))).trans (Q.endpoint_row hη hu _))]
  apply add_le_add le_rfl
  have reindex (s : S) : divergence (fun j => Q.endpoint η s (report j))
        (fun j => P.endpoint η s (report j)) = divergence (Q.endpoint η s) (P.endpoint η s) :=
    report.sum_comp (fun j => rel (Q.endpoint η s j) (P.endpoint η s j))
  simp only [reindex]
  have h := start.sum_comp (fun s => μ s * divergence (Q.endpoint η s) (P.endpoint η s))
  simp only [preserve] at h
  rw [h]
  exact stopped_divergence Q P sup μ hμ stat hη hu

end Kernel
end TwoSAT.Walk

end

section

namespace TwoSAT

deriving instance Fintype for Literal
deriving instance Fintype for Clause

namespace Query

variable {n d : ℕ} {α β : Type}

/-- A joint draw of a finite table, with the required distribution in each entry. -/
private theorem couple_fin (m : ℕ) (f : Fin m → PMF β) :
    ∃ p : PMF (Fin m → β), ∀ i, p.map (fun a => a i) = f i := by
  induction m with
  | zero => exact ⟨PMF.pure Fin.elim0, fun i => i.elim0⟩
  | succ m ih =>
    obtain ⟨tail,ht⟩ := ih (fun i => f i.succ)
    refine ⟨(f 0).bind (fun b => tail.map (Fin.cons b)), ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Fin.cons_zero]
      simp only [show ∀ a : β, (fun _ : Fin m → β => a) = Function.const _ a from fun _ => rfl,
        PMF.map_const, PMF.bind_pure]
    · simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Fin.cons_succ, ht, PMF.bind_const]

private theorem couple_finite [Finite α] (f : α → PMF β) :
    ∃ p : PMF (α → β), ∀ i, p.map (fun a => a i) = f i := by
  classical
  let := Fintype.ofFinite α
  let e := Fintype.equivFin α
  obtain ⟨p,hp⟩ := couple_fin _ (fun i => f (e.symm i))
  refine ⟨p.map (fun b => b ∘ e), fun i => ?_⟩
  simpa only [PMF.map_comp, Function.comp_def, Equiv.symm_apply_apply] using hp (e i)

/-- The complete output law, as represented by a distribution on deterministic trees. -/
def Realizes (k : ℕ) (f : Oracle n d → PMF Bool) : Prop :=
  ∃ p : PMF (Tree n d k), ∀ o, p.map (fun tr => tr.run o) = f o

theorem stop (b : Bool) (k : ℕ) : Realizes (n := n) (d := d) k (fun _ => PMF.pure b) :=
  ⟨PMF.pure (.leaf b), fun _ => PMF.pure_map ..⟩

/-- Randomness drawn independently of the oracle can be sampled before starting. -/
theorem draw {k : ℕ} (p : PMF α) {g : α → Oracle n d → PMF Bool}
    (hg : ∀ a, Realizes k (g a)) : Realizes k (fun o => p.bind (fun a => g a o)) := by
  choose branch hb using hg
  refine ⟨p.bind branch, fun o => ?_⟩
  simp only [PMF.map_bind, hb]

/-- A bounded deterministic computation may select the law of all subsequent choices,
including choices using an exactly computed real-valued clause weight. -/
theorem observe {j k : ℕ} {f : Oracle n d → α} (hf : Bounded j f)
    {g : α → Oracle n d → PMF Bool} (hg : ∀ a, Realizes k (g a)) :
    Realizes (k+j) (fun o => g (f o) o) := by
  classical
  choose branches hb using hg
  let I := Set.range f
  let : Finite I := Set.finite_range f
  obtain ⟨p,hp⟩ := couple_finite (fun a : I => branches a.val)
  let next (b : I → Tree n d k) (a : α) : Tree n d k :=
    if ha : a ∈ Set.range f then b ⟨a,ha⟩ else .leaf false
  choose compiled hc using fun b => hf k (next b)
  refine ⟨p.map compiled, fun o => ?_⟩
  let idx : I := ⟨f o, o, rfl⟩
  have hrun : (fun tr => Tree.run o tr) ∘ compiled =
      (fun tr => Tree.run o tr) ∘ (fun b : I → Tree n d k => b idx) := by
    funext b
    have hit : f o ∈ Set.range f := ⟨o,rfl⟩
    simp only [Function.comp_apply, hc, next, dif_pos hit, idx]
  rw [PMF.map_comp, hrun, ← PMF.map_comp, hp, hb]

end Query
end TwoSAT

end

section

namespace TwoSAT.ClauseLaw

open Finset TwoSAT.Walk TwoSAT.Entropy

variable {I J S V E : Type} [Fintype I] [Fintype J] [Fintype S] [Fintype E]

/-- Push a finite mass function through a label map. -/
noncomputable def mass [DecidableEq S] (label : I → S) (w : I → ℝ) (s : S) :=
  ∑ i, if label i = s then w i else 0

theorem integrate_mass [DecidableEq S] (label : I → S) (w : I → ℝ) (f : S → ℝ) :
    ∑ s, mass label w s * f s = ∑ i, w i * f (label i) := by
  simp only [mass, sum_mul]
  rw [sum_comm]
  simp [ite_mul]

theorem sum_mass [DecidableEq S] (label : I → S) (w : I → ℝ) :
    ∑ s, mass label w s = ∑ i, w i := by simpa using integrate_mass label w (fun _ => 1)

omit [Fintype S] in
theorem mass_nonneg [DecidableEq S] (label : I → S) {w : I → ℝ} (hw : ∀ i, 0 ≤ w i) (s : S) :
    0 ≤ mass label w s := sum_nonneg fun i _ => by split_ifs <;> first | exact hw i | rfl

omit [Fintype S] in
theorem le_mass [DecidableEq S] (label : I → S) {w : I → ℝ} (hw : ∀ i, 0 ≤ w i) (i : I) :
    w i ≤ mass label w (label i) := by
  have hn (j : I) : 0 ≤ (if label j = label i then w j else 0) := by split_ifs <;> simp [hw]
  simpa [mass] using single_le_sum (s := univ) (fun j _ => hn j) (mem_univ i)

theorem data_processing [DecidableEq S] (label : I → S) (a b : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (supp : ∀ i, 0 < a i → 0 < b i) :
    divergence (mass label a) (mass label b) ≤ divergence a b := by
  let row (w : I → ℝ) (s : S) (i : I) := if label i = s then w i else 0
  have h (s : S) : rel (mass label a s) (mass label b s) ≤ ∑ i, row (fun j => rel (a j) (b j)) s i := by
    have hp (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (i : I) : 0 ≤ row w s i := by dsimp [row]; split_ifs <;> simp [hw]
    have hs (i : I) : 0 < row a s i → 0 < row b s i := by
      dsimp [row]; split_ifs
      · exact supp i
      · exact id
    have hl := log_sum (row a s) (row b s) (hp a ha) (hp b hb) hs
    have hv (i : I) : rel (row a s i) (row b s i) = row (fun j => rel (a j) (b j)) s i := by
      dsimp [row]; split_ifs <;> simp [rel]
    simpa only [hv, mass, row] using hl
  exact (sum_le_sum (s := univ) (fun s _ => h s)).trans_eq (sum_mass label _)

def side (u v : E → Literal V) (i : E × Bool) := if i.2 then u i.1 else v i.1
def partner (i : E × Bool) := (i.1,!i.2)
def target (u v : E → Literal V) (i : E × Bool) := (side u v (partner i)).flip

noncomputable def oriented (w : E → ℝ) (i : E × Bool) := w i.1 / 2

theorem sum_oriented (w : E → ℝ) : ∑ i, oriented w i = ∑ e, w e := by
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  simp [oriented]; ring

variable [DecidableEq V] [Fintype V]

noncomputable def seed (u v : E → Literal V) (w : E → ℝ) := mass (side u v) (oriented w)

noncomputable def flow (u v : E → Literal V) (w : E → ℝ) (s t : Literal V) :=
  ∑ i, if side u v i = s ∧ target u v i = t then oriented w i else 0

omit [Fintype V] in
theorem seed_nonneg (u v : E → Literal V) {w : E → ℝ} (hw : ∀ e, 0 ≤ w e) (s) :
    0 ≤ seed u v w s := mass_nonneg _ (fun i => div_nonneg (hw _) (by norm_num)) s

theorem seed_total (u v : E → Literal V) (w : E → ℝ) : ∑ s, seed u v w s = ∑ e, w e :=
  (sum_mass ..).trans (sum_oriented w)

omit [Fintype V] in
theorem flow_nonneg (u v : E → Literal V) {w : E → ℝ} (hw : ∀ e, 0 ≤ w e) (s t) :
    0 ≤ flow u v w s t := sum_nonneg fun i _ => by
      split_ifs <;> first | exact div_nonneg (hw _) (by norm_num) | rfl

theorem flow_row (u v : E → Literal V) (w : E → ℝ) (s) :
    ∑ t, flow u v w s t = seed u v w s := by
  unfold flow seed mass
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  by_cases h : side u v i = s <;> simp [h]

theorem flow_col (u v : E → Literal V) (w : E → ℝ) (t) :
    ∑ s, flow u v w s t = seed u v w t.flip := by
  unfold flow seed mass
  rw [sum_comm, Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro e _
  have eq (a : Literal V) : a.flip = t ↔ a = t.flip :=
    ⟨fun h => by rw [← h]; simp, fun h => by rw [h]; simp⟩
  simp only [Fintype.sum_bool, side, target, partner, oriented, Bool.not_true, Bool.not_false,
    if_true, if_false, Bool.false_eq_true, eq]
  by_cases hu : u e = t.flip <;> by_cases hv : v e = t.flip <;> simp [hu,hv,add_comm]

noncomputable def transition (u v : E → Literal V) (w : E → ℝ) (s t : Literal V) :=
  if seed u v w s = 0 then (if s = t then 1 else 0) else flow u v w s t / seed u v w s

noncomputable def forward (u v : E → Literal V) (w : E → ℝ) (hw : ∀ e, 0 ≤ w e) :
    Kernel (Literal V) where
  prob := transition u v w
  nonneg s t := by
    unfold transition
    split_ifs <;> first | exact div_nonneg (flow_nonneg _ _ hw _ _) (seed_nonneg _ _ hw _) | norm_num
  row s := by
    by_cases hz : seed u v w s = 0 <;> simp [transition, hz, ← sum_div, flow_row]

/-- Under balance the forward implication kernel preserves the literal marginal. -/
theorem stationary (u v : E → Literal V) (w : E → ℝ) (hw : ∀ e, 0 ≤ w e)
    (balance : ∀ s, seed u v w s.flip = seed u v w s) :
    (forward u v w hw).Stationary (seed u v w) := by
  intro t
  have cancel (s : Literal V) : seed u v w s * transition u v w s t = flow u v w s t := by
    by_cases hz : seed u v w s = 0
    · have hle := single_le_sum (s := univ) (fun j _ => flow_nonneg u v hw s j) (mem_univ t)
      rw [flow_row, hz] at hle
      rw [hz,zero_mul]; exact (hle.antisymm (flow_nonneg u v hw s t)).symm
    · simp [transition, hz, mul_div_cancel₀]
  change ∑ s, seed u v w s * transition u v w s t = _
  simp only [cancel, flow_col, balance]

end TwoSAT.ClauseLaw

end

section

namespace TwoSAT.Balance

open Finset TwoSAT.ClauseLaw TwoSAT.Entropy

variable {I S : Type} [Fintype I] [Fintype S] [DecidableEq S]

/-- The unnormalized entropy of the atom weights minus that of the label masses.
For oriented clause incidences the labels are the forbidden literals. -/
noncomputable def penalty (label : I → S) (base w : I → ℝ) :=
  divergence w base - divergence (mass label w) (mass label base)

theorem penalty_nonneg (label : I → S) (base w : I → ℝ) (hb : ∀ i, 0 < base i)
    (hw : ∀ i, 0 ≤ w i) : 0 ≤ penalty label base w :=
  sub_nonneg.mpr (data_processing label w base hw (fun i => (hb i).le) (fun i _ => hb i))

private theorem rel_cont (b : ℝ) : Continuous (fun a => rel a b) := by
  by_cases h : b = 0
  · simp [h,rel,continuous_const]
  · have heq (a : ℝ) : rel a b = a*Real.log a - a*Real.log b := by
      by_cases ha : a = 0
      · simp [ha,rel]
      · simp [rel, Real.log_div ha h, mul_sub]
    simp_rw [heq]
    exact Real.continuous_mul_log.sub (continuous_id.mul_const _)

omit [Fintype S] in
private theorem cont_mass (label : I → S) (s : S) : Continuous (fun w => mass label w s) := by
  apply continuous_finsetSum
  intro i _
  by_cases h : label i = s <;> simp [h, continuous_apply, continuous_const]

theorem penalty_continuous (label : I → S) (base : I → ℝ) : Continuous (penalty label base) := by
  apply Continuous.sub
  · exact continuous_finsetSum _ (fun i _ => (rel_cont (base i)).comp (continuous_apply i))
  · exact continuous_finsetSum _ (fun s _ => (rel_cont (mass label base s)).comp (cont_mass label s))

noncomputable def denominator (label : I → S) (base w : I → ℝ) (i : I) :=
  mass label w (label i) * (base i / mass label base (label i))

omit [Fintype S] in
private theorem den_pos (label : I → S) {base w : I → ℝ}
    (hb : ∀ i, 0 < base i) (hw : ∀ i, 0 ≤ w i) (i : I) (hp : 0 < w i) :
    0 < denominator label base w i :=
  mul_pos (hp.trans_le (le_mass _ hw _)) (div_pos (hb i) ((hb i).trans_le (le_mass _ (fun j => (hb j).le) i)))

theorem penalty_formula (label : I → S) (base w : I → ℝ)
    (hb : ∀ i, 0 < base i) (hw : ∀ i, 0 ≤ w i) :
    penalty label base w = ∑ i, rel (w i) (denominator label base w i) := by
  have iden (i : I) : rel (w i) (denominator label base w i) = rel (w i) (base i) -
      w i * Real.log (mass label w (label i) / mass label base (label i)) := by
    rcases (hw i).eq_or_lt with h | h
    · rw [← h]; simp [rel]
    have hW := h.trans_le (le_mass label hw i)
    have hB := (hb i).trans_le (le_mass label (fun j => (hb j).le) i)
    have hd := den_pos label hb hw i h
    rw [rel, Real.log_div h.ne' hd.ne', denominator,
      Real.log_mul hW.ne' (div_pos (hb i) hB).ne', Real.log_div (hb i).ne' hB.ne', rel,
      Real.log_div h.ne' (hb i).ne', Real.log_div hW.ne' hB.ne']
    ring
  simp only [iden,sum_sub_distrib,penalty]
  congr 1
  exact integrate_mass label w (fun s => Real.log (mass label w s / mass label base s))

omit [Fintype S] in
private theorem mass_mix (label : I → S) (w v : I → ℝ) (a b : ℝ) (s : S) :
    mass label (a • w + b • v) s = a * mass label w s + b * mass label v s := by
  simp only [mass,mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases h : label i = s <;> simp [h]

/-- Convexity of the conditional entropy penalty follows from log-sum at each atom. -/
theorem penalty_convex (label : I → S) (base : I → ℝ) (hb : ∀ i, 0 < base i) :
    ConvexOn ℝ (Set.Ici (0 : I → ℝ)) (penalty label base) := by
  refine ⟨convex_Ici _, ?_⟩
  intro w hw v hv a b ha hb' hab
  have hm : 0 ≤ a • w + b • v := fun i => add_nonneg (mul_nonneg ha (hw i)) (mul_nonneg hb' (hv i))
  rw [penalty_formula label _ _ hb hm, penalty_formula label _ _ hb hw, penalty_formula label _ _ hb hv]
  simp only [smul_eq_mul,mul_sum,← sum_add_distrib]
  apply sum_le_sum
  intro i _
  let x := denominator label base w i
  let y := denominator label base v i
  have dx : 0 ≤ x := mul_nonneg (mass_nonneg _ hw _) (div_nonneg (hb i).le (mass_nonneg _ (fun j => (hb j).le) _))
  have dy : 0 ≤ y := mul_nonneg (mass_nonneg _ hv _) (div_nonneg (hb i).le (mass_nonneg _ (fun j => (hb j).le) _))
  have linear : denominator label base (a • w + b • v) i = a*x+b*y := by
    simp only [denominator,mass_mix,x,y]; ring
  rw [linear, ← rel_scale ha (hw i) (den_pos label hb hw i), ← rel_scale hb' (hv i) (den_pos label hb hv i)]
  apply TwoSAT.Entropy.rel_add_le (mul_nonneg ha (hw i)) (mul_nonneg ha dx)
    (mul_nonneg hb' (hv i)) (mul_nonneg hb' dy)
  · intro h; exact mul_pos (pos_of_mul_pos_left h (hw i)) (den_pos label hb hw i (pos_of_mul_pos_right h ha))
  · intro h; exact mul_pos (pos_of_mul_pos_left h (hv i)) (den_pos label hb hv i (pos_of_mul_pos_right h hb'))

end TwoSAT.Balance

end

section

namespace TwoSAT.Balance

open Set

/-- The threshold form of minimax used in equation (17). The multiplier domain Y may
be unbounded. Compactness is needed only for the feasible box of weights X. -/
theorem minimax_response {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [TopologicalSpace F] [AddCommGroup F]
    [Module ℝ F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {X : Set E} {Y : Set F} (f : E → F → ℝ) (ne : X.Nonempty) (compact : IsCompact X)
    (cx : Convex ℝ X) (cy : Convex ℝ Y)
    (lx : ∀ y ∈ Y, LowerSemicontinuousOn (fun x => f x y) X)
    (qx : ∀ y ∈ Y, QuasiconvexOn ℝ X (fun x => f x y))
    (uy : ∀ x ∈ X, UpperSemicontinuousOn (f x) Y)
    (qy : ∀ x ∈ X, QuasiconcaveOn ℝ Y (f x)) (c : ℝ)
    (reply : ∀ y ∈ Y, ∃ x ∈ X, f x y ≤ c) :
    ∃ x ∈ X, ∀ y ∈ Y, f x y ≤ c := by
  classical
  by_contra none
  have cover : ∃ s : Finset Y, ∀ x ∈ X, ∃ y ∈ s, c < f x y := by
    rw [← LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finset compact lx]
    apply Set.eq_empty_of_forall_notMem
    rintro x ⟨hx, rest⟩
    simp only [mem_iInter, mem_preimage, mem_Iic] at rest
    exact none ⟨x,hx,rest⟩
  obtain ⟨s, hs⟩ := cover
  have small (x) (hx : x ∈ X) : ∃ y ∈ Subtype.val '' (s : Set Y), c < f x y := by
    obtain ⟨i,hi,h⟩ := hs x hx
    exact ⟨i, ⟨i,hi,rfl⟩, h⟩
  obtain ⟨y,hy,h⟩ := Sion.exists_lt_iInf_of_lt_iInf_of_finite ne compact lx qx cy uy qy cx
    ((s.finite_toSet).image Subtype.val) (Subtype.coe_image_subset Y ↑s) small
  obtain ⟨x,hx,hxy⟩ := reply y hy
  exact (h x hx).not_ge hxy

end TwoSAT.Balance

end

section

namespace TwoSAT.Balance

open Finset TwoSAT.ClauseLaw TwoSAT.Entropy TwoSAT.Weights

variable {V E : Type} [DecidableEq V] [Fintype V] [Fintype E]

noncomputable def clausePenalty (u v : E → Literal V) (π w : E → ℝ) :=
  penalty (side u v) (oriented π) (oriented w)

theorem clausePenalty_eq (u v : E → Literal V) (π w : E → ℝ)
    (hπ : ∀ i, 0 < π i) (hw : ∀ i, 0 ≤ w i) :
    clausePenalty u v π w = divergence w π - divergence (seed u v w) (seed u v π) := by
  unfold clausePenalty penalty seed
  congr 1
  change (∑ i : E × Bool, rel (oriented w i) (oriented π i)) = ∑ i, rel (w i) (π i)
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  have h := rel_scale (a := w i) (b := π i) (w := 1/2) (by norm_num) (hw i) (fun _ => hπ i)
  simp only [Fintype.sum_bool, oriented]
  rw [show w i / 2 = 1/2 * w i by ring, show π i / 2 = 1/2 * π i by ring, h]
  ring

theorem clausePenalty_continuous (u v : E → Literal V) (π : E → ℝ) :
    Continuous (clausePenalty u v π) := by
  apply (penalty_continuous (side u v) (oriented π)).comp
  exact continuous_pi fun i => (continuous_apply i.1).div_const 2

theorem clausePenalty_convex (u v : E → Literal V) (π : E → ℝ) (hπ : ∀ i, 0 < π i) :
    ConvexOn ℝ (Set.Icc 0 π) (clausePenalty u v π) := by
  refine ⟨convex_Icc .., ?_⟩
  intro w hw y hy a b ha hb hab
  have C := penalty_convex (side u v) (oriented π) (fun i => div_pos (hπ i.1) (by norm_num))
  have mix : oriented (a • w + b • y) = a • oriented w + b • oriented y := by
    funext i; simp [oriented]; ring
  apply le_trans (le_of_eq (congrArg (penalty (side u v) (oriented π)) mix))
  exact C.2 (fun i => div_nonneg (hw.1 i.1) (by norm_num))
    (fun i => div_nonneg (hy.1 i.1) (by norm_num)) ha hb hab

/-- Testing balance against an arbitrary variable potential is the signed incidence adjoint. -/
theorem pair_linear (u v : E → Literal V) (z : V → ℝ) (w : E → ℝ) :
    ∑ x, z x * imbalance u v w x = ∑ e, w e * (score z (u e) + score z (v e)) := by
  simpa [mul_comm,clauseScore] using (adjoint u v w z).symm

omit [Fintype V] in
/-- Difference of the two literal masses at a variable. -/
theorem seed_difference (u v : E → Literal V) (w : E → ℝ) (x : V) :
    seed u v w ⟨x,true⟩ - seed u v w ⟨x,false⟩ = imbalance u v w x / 2 := by
  simp only [seed,mass,Fintype.sum_prod_type,Fintype.sum_bool, side, oriented,
    if_true, if_false,Bool.false_eq_true,imbalance,← sum_sub_distrib,sum_div]
  apply sum_congr rfl
  intro i _
  rcases ha : u i with ⟨a,sa⟩
  rcases hb : v i with ⟨b,sb⟩
  cases sa <;> cases sb <;> by_cases hx : a=x <;> by_cases hy : b=x <;>
    simp [hx,hy,signOf,Literal.mk.injEq] <;> ring

omit [Fintype V] in
theorem seed_balanced (u v : E → Literal V) (w : E → ℝ) (h : ∀ x, imbalance u v w x = 0) :
    ∀ s, seed u v w s.flip = seed u v w s := by
  rintro ⟨x,b⟩
  have he := seed_difference u v w x
  rw [h,zero_div,sub_eq_zero] at he
  cases b <;> first | exact he | exact he.symm

end TwoSAT.Balance

end

section

namespace TwoSAT.Balance

noncomputable def keepProb (z : ℝ) := Real.exp z / (Real.exp z + Real.exp (-z))
noncomputable def bias (z : ℝ) := 2 * keepProb z - 1

theorem keepProb_pos (z : ℝ) : 0 < keepProb z := by
  unfold keepProb
  positivity

theorem keepProb_neg (z : ℝ) : keepProb (-z) = 1 - keepProb z := by
  unfold keepProb
  rw [Real.exp_neg]
  field_simp
  ring

theorem bias_neg (z : ℝ) : bias (-z) = -bias z := by
  unfold bias
  rw [keepProb_neg]
  ring

theorem bias_abs (z : ℝ) : |bias z| ≤ 1 := by
  unfold bias keepProb
  rw [abs_le]
  constructor
  · have hpos : 0 < Real.exp z + Real.exp (-z) := by positivity
    have : 0 ≤ Real.exp z / (Real.exp z + Real.exp (-z)) := by positivity
    linarith
  · have hpos : 0 < Real.exp z + Real.exp (-z) := by positivity
    have hle : Real.exp z / (Real.exp z + Real.exp (-z)) ≤ 1 := by
      rw [div_le_one hpos]
      linarith [Real.exp_pos (-z)]
    linarith

theorem log_keepProb (z : ℝ) :
    z - Real.log (keepProb z) = -(Real.log (keepProb z * keepProb (-z))) / 2 := by
  have logp (x : ℝ) : Real.log (keepProb x) = x - Real.log (Real.exp x + Real.exp (-x)) := by
    rw [keepProb, Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp]
  rw [Real.log_mul (keepProb_pos _).ne' (keepProb_pos _).ne',logp,logp,neg_neg,add_comm (Real.exp (-z))]
  ring

end TwoSAT.Balance

end

section

namespace TwoSAT.Balance

open Finset TwoSAT.ClauseLaw TwoSAT.Weights TwoSAT.Entropy

variable {V E : Type} [Fintype E] [Fintype V] [DecidableEq V]

theorem seed_integral (u v : E → Literal V) (w : E → ℝ) (f : Literal V → ℝ) :
    ∑ l, seed u v w l * f l = (∑ i, w i * (f (u i) + f (v i))) / 2 := by
  rw [seed, integrate_mass, Fintype.sum_prod_type, sum_div]
  apply sum_congr rfl
  intro i _
  simp [oriented,side]; ring

noncomputable def trial (u v : E → Literal V) (z : V → ℝ) (π : E → ℝ) (i : E) :=
  π i * (keepProb (score z (u i)) * keepProb (score z (v i)))

omit [Fintype E] [Fintype V] [DecidableEq V] in
theorem trial_pos (u v : E → Literal V) (z : V → ℝ) {π : E → ℝ} (hπ : ∀ i, 0 < π i) (i : E) :
    0 < trial u v z π i := mul_pos (hπ i) (mul_pos (keepProb_pos _) (keepProb_pos _))

omit [Fintype E] [Fintype V] [DecidableEq V] in
theorem trial_le (u v : E → Literal V) (z : V → ℝ) {π : E → ℝ} (hπ : ∀ i, 0 ≤ π i) (i : E) :
    trial u v z π i ≤ π i := by
  have h (t : ℝ) : keepProb t ≤ 1 := by linarith [keepProb_neg t, keepProb_pos (-t)]
  exact mul_le_of_le_one_right (hπ i) (mul_le_one₀ (h _) (keepProb_pos _).le (h _))

omit [Fintype E] [Fintype V] [DecidableEq V] in
theorem score_bias (z : V → ℝ) (a : Literal V) :
    score (fun x => bias (z x)) a = bias (score z a) := by
  unfold score
  split_ifs <;> simp [bias_neg]

private theorem mass_tangent {m b p : ℝ} (hm : 0 ≤ m) (hb : 0 ≤ b) (hp : 0 < p)
    (sup : 0 < m → 0 < b) : m-b*p ≤ rel m b - m*Real.log p := by
  rcases hm.eq_or_lt with hz | hm
  · rw [← hz]; simp [rel,mul_nonneg hb hp.le]
  have hbp := sup hm
  have hpos := div_pos hm (mul_pos hbp hp)
  have hh := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hpos) hm.le
  have he : m * (m/(b*p))⁻¹ = b*p := by field_simp
  rw [mul_sub,mul_one,he,Real.log_div hm.ne' (mul_pos hbp hp).ne',Real.log_mul hbp.ne' hp.ne'] at hh
  rw [rel,Real.log_div hm.ne' hbp.ne']
  linarith only [hh]

private theorem numerical_trial (x y : ℝ) :
    keepProb x * keepProb y - (keepProb x * keepProb (-x) + keepProb y * keepProb (-y))/2 =
      (bias x + bias y)^2/8 + (bias x + bias y)/4 := by
  rw [keepProb_neg,keepProb_neg]; unfold bias; ring

/-- The trial vector estimates the multiplier payoff minus the conditional entropy
penalty, as in (20). Isolated literals can have zero mass. -/
theorem trial_payoff (u v : E → Literal V) (z : V → ℝ) (π : E → ℝ) (hπ : ∀ i, 0 < π i) :
    let w := trial u v z π
    (∑ i, π i * ((bias (score z (u i)) + bias (score z (v i)))^2/8 +
      (bias (score z (u i)) + bias (score z (v i)))/4)) ≤
      (∑ i, w i * clauseScore u v z i) - clausePenalty u v π w := by
  let w := trial u v z π
  let p (l : Literal V) := keepProb (score z l) * keepProb (-score z l)
  let m := seed u v w
  let b := seed u v π
  have hw (i : E) : 0 < w i := trial_pos u v z hπ i
  have hlo (l : Literal V) : m l ≤ b l := by
    apply sum_le_sum; intro i _
    by_cases h : side u v i = l
    · simp only [if_pos h]; exact div_le_div_of_nonneg_right (trial_le u v z (fun j => (hπ j).le) i.1) (by norm_num)
    · simp [h]
  have mt := sum_le_sum (s := univ) (fun l _ => mass_tangent
    (seed_nonneg u v (fun i => (hw i).le) l) (seed_nonneg u v (fun i => (hπ i).le) l)
    (show 0 < p l from mul_pos (keepProb_pos _) (keepProb_pos _)) (fun hp => hp.trans_le (hlo l)))
  have part : (∑ i, w i * clauseScore u v z i) - divergence w π =
      -(∑ l, m l * Real.log (p l)) := by
    rw [show (∑ l, m l * Real.log (p l)) = _ from seed_integral u v w (fun l => Real.log (p l))]
    unfold divergence; rw [← sum_sub_distrib,sum_div,← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    have ratio : w i / π i = keepProb (score z (u i)) * keepProb (score z (v i)) := by
      dsimp [w,trial]; field_simp [(hπ i).ne']
    rw [ratio, Real.log_mul (keepProb_pos _).ne' (keepProb_pos _).ne']
    have h1 := log_keepProb (score z (u i))
    have h2 := log_keepProb (score z (v i))
    dsimp only [p,clauseScore]
    nlinarith only [congrArg (fun x : ℝ => w i*x) h1,congrArg (fun x : ℝ => w i*x) h2]
  have value : (∑ l, m l) - (∑ l, b l * p l) =
      ∑ i, π i * ((bias (score z (u i)) + bias (score z (v i)))^2/8 +
        (bias (score z (u i)) + bias (score z (v i)))/4) := by
    rw [show ∑ l, m l = ∑ i, w i from seed_total u v w,
      show (∑ l, b l * p l) = _ from seed_integral u v π p,sum_div,← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    dsimp [w,trial,p]
    rw [← numerical_trial]
    ring
  change _ ≤ (∑ i, w i * clauseScore u v z i) - clausePenalty u v π w
  rw [clausePenalty_eq _ _ _ _ hπ (fun i => (hw i).le),← value]
  simp only [sum_sub_distrib] at mt
  change _ ≤ divergence m b - _ at mt
  change _ ≤ _ - (divergence w π - divergence m b)
  linarith only [mt,part]

end TwoSAT.Balance

end

section

namespace TwoSAT.Balance

open Finset Set

variable {A V E : Type} [Fintype A] [Fintype V] [Fintype E]

noncomputable def coefficient (C : A → E → ℝ) (B : V → E → ℝ)
    (y : (A → ℝ) × (V → ℝ)) (i : E) :=
  (∑ t, y.1 t * C t i) + ∑ x, y.2 x * B x i

omit [Fintype E] in
private theorem coeff_mix (C : A → E → ℝ) (B : V → E → ℝ)
    (y z : (A → ℝ) × (V → ℝ)) (a b : ℝ) (i : E) :
    coefficient C B (a • y + b • z) i = a * coefficient C B y i + b * coefficient C B z i := by
  simp [coefficient,add_mul,mul_assoc,sum_add_distrib,← mul_sum]
  ring

private theorem dot_mix {D : Type} [Fintype D] (x y c : D → ℝ) (a b : ℝ) :
    ∑ i, ((a • x + b • y) i) * c i = a * (∑ i, x i * c i) + b * (∑ i, y i * c i) := by
  simp [add_mul,mul_assoc,sum_add_distrib,← mul_sum]

/-- A mixed assignment and arbitrary real multipliers may choose their own trial
weights. Minimax gives one balanced vector good for every individual assignment. -/
theorem balanced_of_responses [Nonempty A] (π : E → ℝ) (hπ : 0 ≤ π)
    (P : (E → ℝ) → ℝ) (cont : Continuous P) (conv : ConvexOn ℝ (Icc 0 π) P)
    (C : A → E → ℝ) (B : V → E → ℝ) (c : ℝ)
    (response : ∀ p ∈ stdSimplex ℝ A, ∀ z : V → ℝ, ∃ w ∈ Icc 0 π,
      c ≤ (∑ i, w i * coefficient C B (p,z) i) - P w) :
    ∃ w ∈ Icc 0 π, (∀ x, ∑ i, w i * B x i = 0) ∧
      ∀ t, c ≤ (∑ i, w i * C t i) - P w := by
  classical
  let X := Icc 0 π
  let Y := (stdSimplex ℝ A) ×ˢ (Set.univ : Set (V → ℝ))
  let f (w : E → ℝ) (y : (A → ℝ) × (V → ℝ)) := P w - ∑ i, w i * coefficient C B y i
  have cx : Convex ℝ X := conv.1
  have cy : Convex ℝ Y := (convex_stdSimplex ℝ A).prod convex_univ
  have lx (y) (_ : y ∈ Y) : LowerSemicontinuousOn (fun w => f w y) X := by
    exact (cont.sub (continuous_finsetSum _ (fun i _ => (continuous_apply i).mul_const _))).continuousOn.lowerSemicontinuousOn
  have qx (y) (_ : y ∈ Y) : QuasiconvexOn ℝ X (fun w => f w y) := by
    apply ConvexOn.quasiconvexOn
    refine ⟨cx, ?_⟩
    intro v hv w hw a b ha hb hab
    have le := conv.2 hv hw ha hb hab
    dsimp only [f,smul_eq_mul]
    rw [dot_mix]
    simp only [smul_eq_mul] at le
    linarith only [le]
  have uy (w) (_ : w ∈ X) : UpperSemicontinuousOn (f w) Y := by
    have cc : Continuous (f w) := by dsimp [f,coefficient]; fun_prop
    exact cc.continuousOn.upperSemicontinuousOn
  have qy (w) (_ : w ∈ X) : QuasiconcaveOn ℝ Y (f w) := by
    apply ConcaveOn.quasiconcaveOn
    refine ⟨cy, ?_⟩
    intro y hy z hz a b ha hb hab
    have linear : (∑ i, w i * coefficient C B (a • y+b • z) i) =
      a * (∑ i, w i * coefficient C B y i) + b * (∑ i, w i * coefficient C B z i) := by
      simp only [coeff_mix,mul_add,sum_add_distrib,mul_sum]
      congr 1 <;> apply sum_congr rfl <;> intros <;> ring
    dsimp only [f,smul_eq_mul]
    rw [linear]
    nlinarith only [congrArg (fun t : ℝ => t * P w) hab]
  have reply (y) (hy : y ∈ Y) : ∃ w ∈ X, f w y ≤ -c := by
    obtain ⟨w,hw,le⟩ := response y.1 hy.1 y.2
    exact ⟨w,hw,by dsimp [f]; linarith only [le]⟩
  obtain ⟨w,hw,all⟩ := minimax_response (X := X) (Y := Y) f ⟨0,le_rfl,hπ⟩ isCompact_Icc cx cy lx qx uy qy (-c) reply
  have single (t : A) (z : V → ℝ) :
      c ≤ (∑ i, w i * C t i) + (∑ x, z x * ∑ i, w i * B x i) - P w := by
    have h := all (Pi.single t 1,z) ⟨single_mem_stdSimplex ℝ t,Set.mem_univ _⟩
    have eval (i : E) : coefficient C B (Pi.single t 1,z) i =
        C t i + ∑ x, z x * B x i := by simp [coefficient,Pi.single_apply,ite_mul]
    have adj : ∑ i, w i * (∑ x, z x * B x i) = ∑ x, z x * ∑ i, w i * B x i := by
      simp only [mul_sum]
      rw [sum_comm]; apply sum_congr rfl; intros; apply sum_congr rfl; intros; ring
    simp only [f,eval,mul_add,sum_add_distrib,adj] at h
    linarith only [h]
  refine ⟨w,hw,?_,fun t => by simpa using single t 0⟩
  intro x
  by_contra hn
  let t := Classical.choice (inferInstance : Nonempty A)
  let h := ∑ i, w i * B x i
  let a := c - (∑ i, w i * C t i) + P w - 1
  have eq : (a/h)*h = a := div_mul_cancel₀ a hn
  have bad := single t (Pi.single x (a/h))
  simp only [Pi.single_apply,ite_mul,zero_mul,sum_ite_eq',Finset.mem_univ,if_true] at bad
  change c ≤ _ + (a/h)*h - _ at bad
  rw [eq] at bad
  dsimp [a] at bad
  linarith only [bad]

end TwoSAT.Balance

end

section

namespace TwoSAT.Balance

open Finset TwoSAT.Weights

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]

noncomputable def entry (u v : E → Literal V) (x : V) (i : E) :=
  (if (u i).var = x then signOf (u i) else 0) + (if (v i).var = x then signOf (v i) else 0)

noncomputable def cost (u v : E → Literal V) (α : ℝ) (t : V → Bool) (i : E) :=
  α * charge 1 t (u i) (v i)

omit [Fintype V] [DecidableEq V] in
private theorem mult_charge (w r : ℝ) (t : V → Bool) (a b : Literal V) :
    w * charge r t a b = charge (w*r) t a b := by unfold charge; split_ifs <;> simp

omit [Fintype E] in
private theorem by_variable (u v : E → Literal V) (z : V → ℝ) (i : E) :
    ∑ x, z x * entry u v x i = clauseScore u v z i := by
  simp [entry,clauseScore,mul_add,mul_ite,sum_add_distrib,score,signOf]

private theorem coefficient_sum (u v : E → Literal V) (α : ℝ) (w : E → ℝ)
    (p : (V → Bool) → ℝ) (z : V → ℝ) :
    (∑ i, w i * coefficient (cost u v α) (entry u v) (p,z) i) =
    α * (∑ t, p t * ∑ i, charge (w i) t (u i) (v i)) +
    ∑ i, w i * clauseScore u v z i := by
  simp only [coefficient,by_variable,mul_add,sum_add_distrib]
  congr 1
  simp only [cost,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro t _
  apply sum_congr rfl; intro i _
  calc
    _ = α*(p t*(w i * charge 1 t (u i) (v i))) := by ring
    _ = _ := by rw [mult_charge,mul_one]

private theorem imbalance_term (u v : E → Literal V) (π : E → ℝ) (z : V → ℝ) :
    -(∑ x, |imbalance u v π x|) ≤ ∑ i, π i * (bias (score z (u i)) + bias (score z (v i))) := by
  simp_rw [← score_bias]
  rw [← pair_linear,← sum_neg_distrib]
  apply sum_le_sum
  intro x _
  have h := abs_mul (bias (z x)) (imbalance u v π x)
  have hh := mul_le_mul_of_nonneg_right (bias_abs (z x)) (abs_nonneg (imbalance u v π x))
  linarith only [h,hh,neg_abs_le (bias (z x) * imbalance u v π x)]

omit [Fintype V] [DecidableEq V] [Fintype E] in
private theorem weighted_trial_loss (u v : E → Literal V) (z : V → ℝ) (π : E → ℝ)
    (t : V → Bool) (i : E) :
    π i * charge ((1+bias (score z (u i)))*(1+bias (score z (v i)))) t (u i) (v i) =
      4 * charge (trial u v z π i) t (u i) (v i) := by
  unfold charge trial bias
  split_ifs <;> ring

/-- Equation (15) in feasibility form. This vector works for all assignments and
has exactly zero imbalance. The trial vector used against each multiplier may differ. -/
theorem balanced_payoff (u v : E → Literal V) (π : E → ℝ) (hπ : ∀ i, 0 < π i)
    (sπ : ∑ i, π i = 1) {δ α : ℝ} (hδ : 0 ≤ δ) (hu : δ ≤ 1) (hα : 0 < α) (ha : α ≤ 1)
    (far : ∀ t, δ ≤ ∑ i, π i * charge 1 t (u i) (v i)) :
    ∃ w ∈ Set.Icc 0 π, (∀ x, imbalance u v w x = 0) ∧ ∀ t,
      α*δ^2/8 - (∑ x, |imbalance u v π x|)/4 ≤
        α * (∑ i, charge (w i) t (u i) (v i)) - clausePenalty u v π w := by
  let c := α*δ^2/8 - (∑ x, |imbalance u v π x|)/4
  have response (p) (hp : p ∈ stdSimplex ℝ (V → Bool)) (z : V → ℝ) :
      ∃ w ∈ Set.Icc 0 π, c ≤ (∑ i, w i * coefficient (cost u v α) (entry u v) (p,z) i) -
        clausePenalty u v π w := by
    let w := trial u v z π
    refine ⟨w,⟨fun i => (trial_pos u v z hπ i).le,trial_le u v z (fun i => (hπ i).le)⟩,?_⟩
    rw [coefficient_sum]
    let D := ∑ i, π i * (bias (score z (u i)) + bias (score z (v i)))^2
    let L := ∑ t, p t * ∑ i, charge (w i) t (u i) (v i)
    let B := ∑ i, π i * (bias (score z (u i)) + bias (score z (v i)))
    have hD : 0 ≤ D := sum_nonneg fun i _ => mul_nonneg (hπ i).le (sq_nonneg _)
    have hh := (Reassignment.reassignment_bound u v π (fun i => (hπ i).le) sπ
      (fun x => bias (z x)) (fun x => bias_abs _) id p hp.1 hp.2 hu far hδ).2
    simp only [score_bias,id_eq,weighted_trial_loss,← mul_sum,mul_left_comm (p _) 4] at hh
    change δ^2 ≤ D + 2*(4*L) at hh
    have ht := trial_payoff u v z π hπ
    have sum_eq : (∑ i, π i * ((bias (score z (u i)) + bias (score z (v i)))^2/8 +
      (bias (score z (u i)) + bias (score z (v i)))/4)) = D/8 + B/4 := by
      have dist (r x y : ℝ) : r*(x/8+y/4) = r*x/8+r*y/4 := by ring
      simp only [dist,sum_add_distrib,← sum_div,D,B]
    rw [sum_eq] at ht
    have hB := imbalance_term u v π z
    change _ ≤ B at hB
    change c ≤ α*L + _ - _
    dsimp only [c]
    nlinarith only [ht,hB,mul_le_mul_of_nonneg_left hh hα.le,
      mul_le_mul_of_nonneg_right ha hD]
  obtain ⟨w,hw,hB,hC⟩ := balanced_of_responses π (fun i => (hπ i).le) _
    (clausePenalty_continuous u v π) (clausePenalty_convex u v π hπ) (cost u v α) (entry u v) c response
  refine ⟨w,hw,fun x => ?_,fun t => ?_⟩
  · simpa [imbalance,entry,mul_comm] using hB x
  · have eq (i : E) : w i * cost u v α t i = α * charge (w i) t (u i) (v i) := by
      unfold cost; rw [mul_left_comm,mult_charge,mul_one]
    simpa only [eq, ← mul_sum] using hC t

end TwoSAT.Balance

end

section

namespace TwoSAT.Balance

open Finset TwoSAT.Entropy TwoSAT.ClauseLaw TwoSAT.Weights

variable {S V E : Type} [DecidableEq V] [Fintype V] [Fintype E] [Fintype S] [DecidableEq S]

omit [Fintype S] in
theorem mass_scale (label : E → S) (w : E → ℝ) (a : ℝ) (s : S) :
    mass label (fun i => a*w i) s = a*mass label w s := by
  simp only [mass,mul_sum]
  apply sum_congr rfl; intro i _
  split_ifs <;> simp

theorem penalty_scale (label : E → S) (π w : E → ℝ) (hπ : ∀ i, 0 < π i) (hw : ∀ i, 0 ≤ w i)
    {a : ℝ} (ha : 0 ≤ a) : penalty label π (fun i => a*w i) = a*penalty label π w := by
  rw [penalty_formula _ _ _ hπ (fun i => mul_nonneg ha (hw i)),penalty_formula _ _ _ hπ hw,mul_sum]
  apply sum_congr rfl
  intro i _
  have hd : denominator label π (fun j => a*w j) i = a*denominator label π w i := by
    simp [denominator,mass_scale,mul_assoc]
  rw [hd]
  apply rel_scale ha (hw i)
  intro hi
  exact mul_pos (hi.trans_le (le_mass _ hw _))
    (div_pos (hπ i) ((hπ i).trans_le (le_mass _ (fun j => (hπ j).le) i)))

omit [Fintype E] in
private theorem scale_oriented (a : ℝ) (w : E → ℝ) :
    oriented (fun i => a*w i) = fun i => a*oriented w i := by funext i; unfold oriented; ring

omit [Fintype V] in
private theorem seed_scale (u v : E → Literal V) (w : E → ℝ) (a : ℝ) (l : Literal V) :
    seed u v (fun i => a*w i) l = a*seed u v w l := by
  unfold seed; rw [scale_oriented,mass_scale]

private theorem div_bound {I : Type} [Fintype I] (p q : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (sp : ∑ i, p i = 1) {a : ℝ} (ha : 0 < a)
    (bound : ∀ i, p i ≤ a*q i) : divergence p q ≤ Real.log a := by
  change (∑ i, rel (p i) (q i)) ≤ _
  calc
    _ ≤ ∑ i, p i * Real.log a := by
      apply sum_le_sum; intro i _
      rcases (hp i).eq_or_lt with hz | h
      · simp [← hz,rel]
      · have hq : 0 < q i := pos_of_mul_pos_right (h.trans_le (bound i)) ha.le
        exact mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos h hq)
          ((div_le_iff₀ hq).mpr (bound i))) (hp i)
    _ = _ := by rw [← sum_mul,sp,one_mul]

omit [DecidableEq V] [Fintype V] in
private theorem total_two (u v : E → Literal V) (w : E → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, charge (w i) (fun _ => false) (u i) (v i)) +
      (∑ i, charge (w i) (fun _ => true) (u i) (v i)) ≤ ∑ i, w i := by
  rw [← sum_add_distrib]; apply sum_le_sum
  intro i _
  rcases hu : u i with ⟨x,a⟩
  rcases hv : v i with ⟨y,b⟩
  cases a <;> cases b <;> simp [charge,Literal.eval,hw]

/-- The balanced clause law from Theorem 4.1, with the density, loss, conditional
divergence and seed divergence bounds used for the endpoint walk comparison. -/
theorem balanced_distribution (u v : E → Literal V) (π : E → ℝ) (hπ : ∀ i, 0 < π i)
    (sπ : ∑ i, π i = 1) {δ α : ℝ} (hδ : 0 < δ) (hu : δ ≤ 1) (hα : 0 < α) (ha : α ≤ 1)
    (far : ∀ t, δ ≤ ∑ i, π i * charge 1 t (u i) (v i))
    (near : (∑ x, |imbalance u v π x|) ≤ α*δ^2/400) :
    let h := δ^2/1600
    ∃ p : E → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧ (∀ x, imbalance u v p x = 0) ∧
      (∀ i, p i ≤ π i/(2*h)) ∧ (∀ t, h ≤ ∑ i, charge (p i) t (u i) (v i)) ∧
      clausePenalty u v π p ≤ α/2 ∧ divergence (seed u v p) (seed u v π) ≤ Real.log (1/(2*h)) := by
  let h := δ^2/1600
  have hpos : 0 < h := by dsimp [h]; positivity
  obtain ⟨w,hw,bal,pay⟩ := balanced_payoff u v π hπ sπ hδ.le hu hα ha far
  let W := ∑ i, w i
  let P := clausePenalty u v π w
  have hP : 0 ≤ P := penalty_nonneg _ _ _ (fun i => div_pos (hπ i.1) (by norm_num))
    (fun i => div_nonneg (hw.1 i.1) (by norm_num))
  have massle : W ≤ 1 := (sum_le_sum fun i _ => hw.2 i).trans_eq sπ
  have bound (t : V → Bool) : α*h + P ≤ α * ∑ i, charge (w i) t (u i) (v i) := by
    have base : α*h ≤ α*δ^2/8 - (∑ x, |imbalance u v π x|)/4 := by
      dsimp [h]; nlinarith only [near, mul_pos hα (sq_pos_of_pos hδ)]
    linarith only [base,pay t]
  have combined : 2*(α*h+P) ≤ α*W := by
    have hh := mul_le_mul_of_nonneg_left (total_two u v w hw.1) hα.le
    linarith only [bound (fun _ => false), bound (fun _ => true),hh]
  have hW : 2*h ≤ W := (mul_le_mul_iff_right₀ hα).mp (by linarith only [combined,hP])
  have pos : 0 < W := (by positivity : 0 < 2*h).trans_le hW
  let p (i : E) := W⁻¹*w i
  have hp (i : E) : 0 ≤ p i := mul_nonneg (inv_pos.mpr pos).le (hw.1 i)
  have sp : ∑ i, p i = 1 := by dsimp only [p]; rw [← mul_sum]; exact inv_mul_cancel₀ pos.ne'
  refine ⟨p,hp,sp,?_,?_,?_,?_,?_⟩
  · intro x
    simp only [p,imbalance,mul_left_comm _ W⁻¹,← mul_sum]
    change W⁻¹*imbalance u v w x = 0
    rw [bal,mul_zero]
  · intro i
    change W⁻¹ * w i ≤ π i/(2*h)
    rw [← div_eq_inv_mul]
    exact div_le_div₀ (hπ i).le (hw.2 i) (by positivity) hW
  · intro t
    have L := (mul_le_mul_iff_right₀ hα).mp (le_trans (le_add_of_nonneg_right hP) (bound t))
    have eq (i : E) : charge (p i) t (u i) (v i) = W⁻¹ * charge (w i) t (u i) (v i) := by
      unfold p charge; split_ifs <;> simp
    simp_rw [eq]
    rw [← mul_sum, ← div_eq_inv_mul]
    apply (le_div_iff₀ pos).mpr
    exact (mul_le_of_le_one_right hpos.le massle).trans L
  · change penalty (side u v) (oriented π) (oriented p) ≤ α/2
    simp only [p,scale_oriented]
    rw [penalty_scale (side u v) (oriented π) (oriented w) (fun i => div_pos (hπ i.1) (by norm_num))
      (fun i => div_nonneg (hw.1 i.1) (by norm_num)) (inv_pos.mpr pos).le, ← div_eq_inv_mul]
    apply (div_le_iff₀ pos).mpr
    change P ≤ α/2*W
    nlinarith only [combined,mul_pos hα hpos]
  · apply div_bound _ _ (seed_nonneg u v hp) ((seed_total u v p).trans sp) (by positivity)
    intro l
    have hle : seed u v w l ≤ seed u v π l := by
      apply sum_le_sum; intro i _
      by_cases he : side u v i = l
      · simp only [if_pos he]; exact div_le_div_of_nonneg_right (hw.2 i.1) (by norm_num)
      · simp [he]
    rw [show seed u v p l = _ from seed_scale u v w W⁻¹ l, ← div_eq_inv_mul,one_div,← div_eq_inv_mul]
    exact div_le_div₀ (seed_nonneg _ _ (fun i => (hπ i).le) _) hle (by positivity) hW

end TwoSAT.Balance

end

section

namespace TwoSAT.Walk.Kernel

open Finset TwoSAT.Entropy

variable {S : Type} [Fintype S] [DecidableEq S]

noncomputable def lazy (K : Kernel S) : Kernel S where
  prob s j := (if s = j then 1/2 else 0) + (1/2)*K.prob s j
  nonneg s j := add_nonneg (by split_ifs <;> norm_num) (mul_nonneg (by norm_num) (K.nonneg ..))
  row s := by simp [sum_add_distrib,← mul_sum,K.row]; norm_num

theorem lazy_stationary (K : Kernel S) (μ : S → ℝ) (h : K.Stationary μ) : K.lazy.Stationary μ := by
  intro t
  change (∑ s, μ s * ((if s = t then 1/2 else 0)+(1/2)*K.prob s t)) = μ t
  have split (s : S) : μ s * ((1/2) * K.prob s t) = (μ s * K.prob s t)*(1/2) := by ring
  simp only [mul_add,mul_ite,mul_zero,sum_add_distrib,sum_ite_eq',mem_univ,if_true,split,← sum_mul,h t]; ring

end TwoSAT.Walk.Kernel

namespace TwoSAT.ClauseLaw

open Finset TwoSAT.Entropy TwoSAT.Balance TwoSAT.Walk

variable {I S V E : Type} [Fintype I] [DecidableEq S] [Fintype S] [Fintype E] [Fintype V] [DecidableEq V]

noncomputable def conditional (label : I → S) (a : I → ℝ) (s : S) (i : I) :=
  if label i = s then a i / mass label a s else 0

omit [Fintype S] in
private theorem conditional_nonneg (label : I → S) (a : I → ℝ) (ha : ∀ i, 0 ≤ a i) (s i) :
    0 ≤ conditional label a s i := by
  unfold conditional; split_ifs <;> first | exact div_nonneg (ha _) (mass_nonneg _ ha _) | rfl

omit [Fintype S] in
private theorem cond_support (label : I → S) (a b : I → ℝ) (_ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 < b i) (s i) : 0 < conditional label a s i → 0 < conditional label b s i := by
  by_cases h : label i = s
  · subst s
    simp only [conditional,if_true]
    exact fun _ => div_pos (hb i) ((hb i).trans_le (le_mass label (fun j => (hb j).le) i))
  · simp [conditional,h]

/-- Weighted conditional divergences sum to the penalty in (11). -/
theorem conditional_divergence (label : I → S) (π w : I → ℝ) (hb : ∀ i, 0 < π i)
    (hw : ∀ i, 0 ≤ w i) :
    ∑ s, mass label w s * divergence (conditional label w s) (conditional label π s) =
      penalty label π w := by
  rw [penalty_formula label π w hb hw]
  change (∑ s, mass label w s * ∑ i, rel _ _) = _
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  have split (s : S) : mass label w s * rel (conditional label w s i) (conditional label π s i) =
      if label i = s then rel (w i) (denominator label π w i) else 0 := by
    by_cases h : label i = s
    · subst s
      simp only [conditional,if_true,denominator]
      by_cases hz : mass label w (label i) = 0
      · have h0 := le_mass label hw i
        rw [hz] at h0
        simp [hz,h0.antisymm (hw i),rel]
      · have he : w i / mass label w (label i) / (π i / mass label π (label i)) =
            w i / (mass label w (label i) * (π i / mass label π (label i))) := by ring
        unfold rel
        rw [he,← mul_assoc,mul_div_cancel₀ _ hz]
    · simp [conditional,h,rel]
  simp [split]

omit [Fintype V] in
private theorem cond_push (u v : E → Literal V) (w : E → ℝ) (s t : Literal V)
    (h : seed u v w s ≠ 0) :
    mass (target u v) (conditional (side u v) (oriented w) s) t = transition u v w s t := by
  rw [transition,if_neg h,flow,sum_div]
  apply sum_congr rfl
  intro i _
  by_cases h1 : side u v i = s <;> by_cases h2 : target u v i = t <;>
    simp [h1,h2,conditional,seed]

theorem lazy_support (u v : E → Literal V) (π w : E → ℝ) (hb : ∀ i, 0 < π i)
    (hw : ∀ i, 0 ≤ w i) : (forward u v w hw).lazy.Supports (forward u v π (fun i => (hb i).le)).lazy := by
  intro s t hpos
  change 0 < (if s=t then (1/2:ℝ) else 0)+(1/2)*transition u v π s t
  by_cases heq : s=t
  · rw [if_pos heq]
    exact add_pos_of_pos_of_nonneg (by norm_num) (mul_nonneg (by norm_num)
      ((forward u v π (fun i => (hb i).le)).nonneg s t))
  · change 0 < (if s=t then (1/2:ℝ) else 0)+(1/2)*transition u v w s t at hpos
    simp only [if_neg heq,zero_add] at hpos ⊢
    by_cases hz : seed u v w s = 0
    · simp [transition,hz,heq] at hpos
    have flowPos : 0 < flow u v w s t :=
      (div_pos_iff_of_pos_right (lt_of_le_of_ne (seed_nonneg _ _ hw _) (Ne.symm hz))).mp
        (by simpa [transition,hz] using pos_of_mul_pos_right hpos (by norm_num))
    obtain ⟨i,_,hi⟩ := (sum_pos_iff_of_nonneg (fun i _ => (show 0 ≤
      (if side u v i = s ∧ target u v i = t then oriented w i else 0) by
        split_ifs <;> first | exact div_nonneg (hw _) (by norm_num) | rfl))).mp flowPos
    have hit : side u v i = s ∧ target u v i = t := by by_contra h; simp [h] at hi
    have bp : 0 < flow u v π s t := by
      apply lt_of_lt_of_le _ (single_le_sum (s := univ) (f := fun j =>
        if side u v j = s ∧ target u v j = t then oriented π j else 0) _ (mem_univ i))
      · simpa [hit,oriented] using div_pos (hb i.1) (by norm_num : (0:ℝ)<2)
      · intro j _; split_ifs <;> first | exact div_nonneg (hb _).le (by norm_num) | rfl
    have hbp : 0 < seed u v π s := by
      rw [← flow_row u v π s]
      exact bp.trans_le (single_le_sum (fun j _ => flow_nonneg _ _ (fun i => (hb i).le) s j) (mem_univ t))
    rw [transition,if_neg hbp.ne']
    exact mul_pos (by norm_num) (div_pos bp hbp)

/-- Laziness charges half a conditional clause divergence per step in expectation. -/
theorem lazy_divergence (u v : E → Literal V) (π w : E → ℝ) (hb : ∀ i, 0 < π i)
    (hw : ∀ i, 0 ≤ w i) :
    let Q := (forward u v w hw).lazy
    let P := (forward u v π (fun i => (hb i).le)).lazy
    (∑ s, seed u v w s * divergence (Q.prob s) (P.prob s)) ≤ clausePenalty u v π w / 2 := by
  let A := oriented w
  let B := oriented π
  let label := side u v
  have ha (i : E × Bool) : 0 ≤ A i := div_nonneg (hw i.1) (by norm_num)
  have hB (i : E × Bool) : 0 < B i := div_pos (hb i.1) (by norm_num)
  have row (s : Literal V) (ht : 0 < seed u v w s) :
      divergence ((forward u v w hw).lazy.prob s) ((forward u v π (fun i => (hb i).le)).lazy.prob s) ≤
        (1/2)*divergence (conditional label A s) (conditional label B s) := by
    have hπ : 0 < seed u v π s := by
      obtain ⟨i,_,hi⟩ := (sum_pos_iff_of_nonneg (fun i _ => (show 0 ≤
        (if label i = s then A i else 0) by split_ifs <;> first | exact ha i | rfl))).mp ht
      have he : label i = s := by by_contra h; simp [h] at hi
      subst s
      exact (hB i).trans_le (le_mass label (fun j => (hB j).le) i)
    have dp := data_processing (target u v) _ _ (conditional_nonneg label A ha s)
      (conditional_nonneg label B (fun i => (hB i).le) s) (cond_support label A B ha hB s)
    have qa : mass (target u v) (conditional label A s) = transition u v w s :=
      funext (fun t => cond_push u v w s t ht.ne')
    have pb : mass (target u v) (conditional label B s) = transition u v π s :=
      funext (fun t => cond_push u v π s t hπ.ne')
    rw [qa,pb] at dp
    apply le_trans _ (mul_le_mul_of_nonneg_left dp (by norm_num : (0:ℝ) ≤ 1/2))
    apply mix_identity _ _ _ (fun j => by split_ifs <;> norm_num)
      ((forward u v w hw).nonneg s) ((forward u v π (fun i => (hb i).le)).nonneg s) _ (by norm_num)
    intro j hpos
    change 0 < transition u v w s j at hpos
    change 0 < transition u v π s j
    rw [← qa] at hpos
    rw [← pb]
    obtain ⟨i,_,hi⟩ := (sum_pos_iff_of_nonneg (fun i _ => (show 0 ≤
      (if target u v i = j then conditional label A s i else 0) by
        split_ifs <;> first | exact conditional_nonneg label A ha s i | rfl))).mp hpos
    by_cases he : target u v i = j
    · simp only [if_pos he] at hi
      have hh := cond_support label A B ha hB s i hi
      subst j
      exact hh.trans_le (le_mass _ (conditional_nonneg label B (fun i => (hB i).le) s) i)
    · simp [he] at hi
  have total := conditional_divergence label B A hB ha
  rw [show clausePenalty u v π w = _ from total.symm,sum_div]
  apply sum_le_sum
  intro s _
  rcases (seed_nonneg u v hw s).eq_or_lt with h | h
  · change _ ≤ seed u v w s * _ / 2
    simp [← h]
  · exact (mul_le_mul_of_nonneg_left (row s h) h.le).trans_eq (by change _ = seed u v w s * _ / 2; ring)

omit [Fintype V] in
theorem seed_support (u v : E → Literal V) (π w : E → ℝ) (hb : ∀ i, 0 < π i)
    (hw : ∀ i, 0 ≤ w i) (s : Literal V) (hs : 0 < seed u v w s) : 0 < seed u v π s := by
  obtain ⟨i,_,hi⟩ := (sum_pos_iff_of_nonneg (fun i _ => (show 0 ≤
    (if side u v i = s then oriented w i else 0) by
      split_ifs <;> first | exact div_nonneg (hw _) (by norm_num) | rfl))).mp hs
  have hit : side u v i = s := by by_contra h; simp [h] at hi
  subst s
  exact (div_pos (hb i.1) (by norm_num : (0:ℝ)<2)).trans_le
    (le_mass (side u v) (w := oriented π) (fun j => div_nonneg (hb j.1).le (by norm_num)) i)

/-- Lemma 6.1 for the actual lazy implication kernels. A bijective endpoint
relabeling and any seed permutation preserving the balanced law are permitted. -/
theorem joint_clause_divergence (u v : E → Literal V) (π w : E → ℝ) (hb : ∀ i, 0 < π i)
    (hw : ∀ i, 0 ≤ w i) (bal : ∀ x, TwoSAT.Weights.imbalance u v w x = 0)
    (start report : Literal V ≃ Literal V) (pres : ∀ s, seed u v w (start s) = seed u v w s)
    {η : ℝ} (hη : 0 < η) (hu : η < 1) :
    let Q := (forward u v w hw).lazy
    let P := (forward u v π (fun i => (hb i).le)).lazy
    divergence (fun a : Literal V × Literal V =>
      seed u v w a.1 * Q.endpoint η (start a.1) (report a.2))
      (fun a => seed u v π a.1 * P.endpoint η (start a.1) (report a.2)) ≤
      divergence (seed u v w) (seed u v π) + ((1-η)/(2*η)) * clausePenalty u v π w := by
  let Q := (forward u v w hw).lazy
  let P := (forward u v π (fun i => (hb i).le)).lazy
  have sm := seed_support u v π w hb hw
  have stat := Kernel.lazy_stationary _ _ (stationary u v w hw (seed_balanced u v w bal))
  apply (Kernel.joint_endpoint_bound Q P (lazy_support u v π w hb hw) _ _
    (seed_nonneg u v hw) sm stat start report pres hη hu).trans
  apply add_le_add le_rfl
  exact (mul_le_mul_of_nonneg_left (lazy_divergence u v π w hb hw)
    (div_nonneg (sub_nonneg.mpr hu.le) hη.le)).trans_eq (by ring)

end TwoSAT.ClauseLaw

end

section

namespace TwoSAT.Walk.Kernel

open Finset TwoSAT.Entropy

variable {S : Type} [Fintype S] [DecidableEq S]

noncomputable def endpointAffinity (K : Kernel S) (η : ℝ) (e : S ≃ S) (s : S) :=
  affinity (K.endpoint η s) (fun j => K.endpoint η s (e j))

theorem affinity_bounds (K : Kernel S) {η : ℝ} (hη : 0 < η) (hu : η < 1) (e : S ≃ S) (s : S) :
    0 ≤ K.endpointAffinity η e s ∧ K.endpointAffinity η e s ≤ 1 := by
  constructor
  · exact sum_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · have hp := K.endpoint_nonneg hη hu s
    have hs := (e.sum_comp (K.endpoint η s)).trans (K.endpoint_row hη hu s)
    simpa only [endpointAffinity,K.endpoint_row hη hu,hs,Real.sqrt_one,one_mul] using
      affinity_le (K.endpoint η s) (fun j => K.endpoint η s (e j)) hp (fun j => hp _)

/-- Joint concavity of Hellinger affinity applied to the first step of a stopped walk. -/
theorem affinity_super (K : Kernel S) {η : ℝ} (hη : 0 < η) (hu : η < 1) (e : S ≃ S) (s : S) :
    (1-η) * ∑ i, K.prob s i * K.endpointAffinity η e i ≤ K.endpointAffinity η e s := by
  let r := 1-η
  have hr : 0 ≤ r := sub_nonneg.mpr hu.le
  let m (i j : S) := (r*K.prob s i)*K.endpoint η i j
  have hm (i j : S) : 0 ≤ m i j := mul_nonneg (mul_nonneg hr (K.nonneg ..)) (K.endpoint_nonneg hη hu ..)
  have sub (j : S) : (∑ i, m i j) ≤ K.endpoint η s j := by
    have smp : (∑ i, m i j) = (1-η)*∑ i, K.prob s i * K.endpoint η i j := by
      simp [m,r,mul_assoc,mul_sum]
    rw [K.endpoint_rec hη hu,smp]
    exact le_add_of_nonneg_left (mul_nonneg hη.le (by split_ifs <;> norm_num))
  have point (i j : S) : √(m i j)*√(m i (e j)) =
      r*(K.prob s i * (√(K.endpoint η i j)*√(K.endpoint η i (e j)))) := by
    have h := mul_nonneg hr (K.nonneg s i)
    simp only [m,Real.sqrt_mul h]
    calc
      _ = (√(r*K.prob s i))^2 * (√(K.endpoint η i j)*√(K.endpoint η i (e j))) := by ring
      _ = _ := by rw [Real.sq_sqrt h]; ring
  have column (j : S) : (∑ i, √(m i j)*√(m i (e j))) ≤ √(K.endpoint η s j)*√(K.endpoint η s (e j)) :=
    (Real.sum_sqrt_mul_sqrt_le univ (fun i => hm i j) (fun i => hm i (e j))).trans
      (mul_le_mul (Real.sqrt_le_sqrt (sub j)) (Real.sqrt_le_sqrt (sub (e j))) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have H := sum_le_sum (s := univ) (fun j _ => column j)
  simp only [point] at H
  rw [sum_comm] at H
  simpa only [endpointAffinity,affinity,mul_sum,r] using H

noncomputable def energy (K : Kernel S) (μ f : S → ℝ) :=
  ∑ s, μ s * ∑ t, K.prob s t * (f s - f t)^2

omit [DecidableEq S] in
theorem stationary_mean (K : Kernel S) {μ : S → ℝ} (stat : K.Stationary μ) (f : S → ℝ) :
    (∑ s, μ s * ∑ t, K.prob s t * f t) = ∑ t, μ t * f t := by
  simp only [mul_sum, ← mul_assoc]
  rw [sum_comm]
  simp only [← sum_mul,show ∀ t, ∑ s, μ s * K.prob s t = μ t from stat]

omit [DecidableEq S] in
theorem energy_formula (K : Kernel S) {μ : S → ℝ} (stat : K.Stationary μ) (f : S → ℝ) :
    K.energy μ f = 2 * ∑ s, μ s * (f s * (f s - ∑ t, K.prob s t * f t)) := by
  have row (s : S) : (∑ t, K.prob s t * (f s-f t)^2) =
      (f s)^2 - 2*f s*(∑ t, K.prob s t*f t) + ∑ t, K.prob s t*(f t)^2 := by
    have he (t : S) : K.prob s t * (f s - f t)^2 =
        (K.prob s t * (f s)^2 - (2*f s)*(K.prob s t*f t)) + K.prob s t*(f t)^2 := by ring
    simp only [he,sum_add_distrib,sum_sub_distrib,← sum_mul,← mul_sum,K.row,one_mul]
  have mom := K.stationary_mean stat (fun t => (f t)^2)
  simp only [energy,row,mul_add,sum_add_distrib]
  rw [mom]
  simp only [mul_sub,sum_sub_distrib,mul_sum]
  ring_nf
  rw [sum_mul]; ring

theorem lazy_average (K : Kernel S) (f : S → ℝ) (s : S) :
    (∑ t, K.lazy.prob s t * f t) = (f s + ∑ t, K.prob s t * f t)/2 := by
  have he (t : S) : K.lazy.prob s t * f t =
      (if s=t then f t/2 else 0)+(K.prob s t*f t)/2 := by
    change ((if s=t then 1/2 else 0)+1/2*K.prob s t)*f t = _
    split_ifs <;> ring
  simp only [he,sum_add_distrib,sum_ite_eq,mem_univ,if_true,← sum_div]
  ring

/-- The first energy estimate in Lemma 5.3. -/
theorem lazy_affinity_energy (K : Kernel S) (μ : S → ℝ) (hp : ∀ s, 0 ≤ μ s)
    (hs : ∑ s, μ s = 1) (stat : K.Stationary μ) {η : ℝ} (hη : 0 < η) (hu : η < 1) (e : S ≃ S) :
    K.energy μ (K.lazy.endpointAffinity η e) ≤ 4*(η/(1-η)) := by
  let a := K.lazy.endpointAffinity η e
  let g s := ∑ t, K.prob s t * a t
  let c := η/(1-η)
  have hbound (s) := K.lazy.affinity_bounds hη hu e s
  have diff (s : S) : g s - a s ≤ 2*c := by
    have hh := K.lazy.affinity_super hη hu e s
    rw [K.lazy_average] at hh
    change (1-η)*((a s + g s)/2) ≤ a s at hh
    have h2 := mul_le_mul_of_nonneg_left (hbound s).2 hη.le
    have hden : 0 < 1-η := sub_pos.mpr hu
    have he : (2*c)*(1-η) = 2*η := by dsimp [c]; field_simp
    apply (le_of_mul_le_mul_right _ hden)
    nlinarith only [hh,h2,he]
  have he (s : S) : μ s*(a s*(a s-g s)) = μ s*((1-a s)*(g s-a s)) - μ s*g s + μ s*a s := by ring
  have same := K.stationary_mean stat a
  change ∑ s, μ s*g s = ∑ s, μ s*a s at same
  rw [energy_formula K stat]
  change 2*(∑ s, μ s*(a s*(a s-g s))) ≤ 4*c
  simp only [he,sum_add_distrib,sum_sub_distrib,same,sub_add_cancel]
  have hc : 0 ≤ 2*c := by dsimp [c]; positivity
  have point (s : S) : μ s * ((1-a s)*(g s-a s)) ≤ μ s*(2*c) := by
    apply mul_le_mul_of_nonneg_left _ (hp s)
    have ha := hbound s
    exact (mul_le_mul_of_nonneg_left (diff s) (sub_nonneg.mpr ha.2)).trans
      (mul_le_of_le_one_left hc (by linarith only [ha.1]))
  have hh := sum_le_sum (s := univ) (fun s _ => point s)
  rw [← sum_mul,hs,one_mul] at hh
  linarith

end TwoSAT.Walk.Kernel

end

section

namespace TwoSAT.ClauseLaw

open Finset TwoSAT.Walk TwoSAT.Balance

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]

def flipPerm : Literal V ≃ Literal V :=
  ⟨Literal.flip,Literal.flip,Literal.flip_flip,Literal.flip_flip⟩

theorem source_flow (u v : E → Literal V) (w : E → ℝ) (hw : ∀ i, 0 ≤ w i) (s t : Literal V) :
    seed u v w s * (forward u v w hw).prob s t = flow u v w s t := by
  change seed u v w s * transition u v w s t = _
  by_cases hz : seed u v w s = 0
  · have hle := single_le_sum (s := univ) (fun j _ => flow_nonneg u v hw s j) (mem_univ t)
    rw [flow_row,hz] at hle
    rw [hz,zero_mul]; exact (hle.antisymm (flow_nonneg u v hw s t)).symm
  · simp [transition,hz,mul_div_cancel₀]

theorem arc_integral (u v : E → Literal V) (w : E → ℝ) (hw : ∀ i, 0 ≤ w i)
    (f : Literal V → Literal V → ℝ) :
    (∑ s, seed u v w s * ∑ t, (forward u v w hw).prob s t * f s t) =
      ∑ i, (w i/2)*(f (u i) (v i).flip + f (v i) (u i).flip) := by
  simp only [mul_sum,← mul_assoc,source_flow]
  have row (s : Literal V) : (∑ t, flow u v w s t * f s t) =
      ∑ i, if side u v i = s then oriented w i * f s (target u v i) else 0 := by
    simp only [flow,sum_mul]
    rw [sum_comm]
    apply sum_congr rfl; intro i _
    by_cases h : side u v i = s <;> simp [h,ite_mul]
  simp_rw [row]
  rw [sum_comm,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  simp [oriented,side,target,partner,mul_add,add_comm]

theorem energy_flip (u v : E → Literal V) (w : E → ℝ) (hw : ∀ i, 0 ≤ w i)
    (f : Literal V → ℝ) :
    (forward u v w hw).energy (seed u v w) (fun s => f s.flip) =
      (forward u v w hw).energy (seed u v w) f := by
  simp only [Kernel.energy, arc_integral, Literal.flip_flip]
  apply sum_congr rfl
  intro i _; ring

/-- Both estimates of Lemma 5.3 in the clause notation of the paper. -/
theorem affinity_difference (u v : E → Literal V) (w : E → ℝ) (hw : ∀ i, 0 ≤ w i)
    (sw : ∑ i, w i = 1) (bal : ∀ x, TwoSAT.Weights.imbalance u v w x = 0)
    {η : ℝ} (hη : 0 < η) (half : η ≤ 1/2) :
    let a := (forward u v w hw).lazy.endpointAffinity η flipPerm
    let d := fun s => a s.flip - a s
    (∀ s, d s.flip = -d s) ∧ (∑ i, w i * (d (u i)+d (v i))^2) ≤ 32*η := by
  let K := forward u v w hw
  let μ := seed u v w
  let a := K.lazy.endpointAffinity η flipPerm
  let b (s : Literal V) := a s.flip
  let d (s : Literal V) := b s - a s
  have hd (s : Literal V) : d s.flip = -d s := by simp [d,b]
  refine ⟨hd,?_⟩
  have stat := stationary u v w hw (seed_balanced u v w bal)
  have bound := K.lazy_affinity_energy μ (seed_nonneg u v hw) ((seed_total u v w).trans sw)
    stat hη (by linarith) flipPerm
  change K.energy μ a ≤ _ at bound
  have cauchy : K.energy μ d ≤ 2*K.energy μ b + 2*K.energy μ a := by
    have he (s t : Literal V) : (d s-d t)^2 ≤ 2*(b s-b t)^2 + 2*(a s-a t)^2 := by
      dsimp only [d]
      nlinarith only [sq_nonneg ((b s-b t)+(a s-a t))]
    have ht := sum_le_sum (s := univ) (fun s _ => mul_le_mul_of_nonneg_left
      (sum_le_sum (s := univ) (fun t _ => mul_le_mul_of_nonneg_left (he s t) (K.nonneg s t)))
      (seed_nonneg u v hw s))
    simpa only [Kernel.energy,μ,mul_add,sum_add_distrib,mul_left_comm _ (2:ℝ),← mul_sum] using ht
  have eq : K.energy μ b = K.energy μ a := energy_flip u v w hw a
  have ed : K.energy μ d = ∑ i, w i * (d (u i)+d (v i))^2 := by
    change (∑ s, seed u v w s * ∑ t, (forward u v w hw).prob s t * (d s-d t)^2) = _
    rw [arc_integral]
    apply sum_congr rfl
    intro i _
    rw [hd,hd]; ring
  change _ ≤ 32*η
  rw [← ed]
  have frac : η/(1-η) ≤ 2*η := (div_le_iff₀ (by linarith)).mpr (by
    nlinarith only [mul_le_mul_of_nonneg_left half hη.le])
  linarith only [cauchy,eq,bound,frac]

end TwoSAT.ClauseLaw

end

section

namespace TwoSAT.Threshold

open MeasureTheory Set

/-- Uniform threshold probability on [α, β], using Lebesgue outer measure so
the first bound also applies to arbitrary completion rules. -/
noncomputable def chance (α β : ℝ) (E : Set ℝ) : ENNReal :=
  volume (Icc α β ∩ E) / ENNReal.ofReal (β - α)

private theorem boundByInterval {α β lo hi b : ℝ} {E : Set ℝ}
    (hβ : α < β) (sub : Icc α β ∩ E ⊆ Ico lo hi) (width : hi - lo ≤ b) :
    chance α β E ≤ ENNReal.ofReal (b / (β - α)) := by
  have hvol := measure_mono (μ := (volume : Measure ℝ)) sub
  rw [Real.volume_Ico] at hvol
  rw [chance, ENNReal.ofReal_div_of_pos (sub_pos.mpr hβ)]
  exact ENNReal.div_le_div_right (hvol.trans (ENNReal.ofReal_le_ofReal width)) _

/-- A completed value indicates whether the endpoint of the forbidden pair is
true. When its absolute score exceeds the threshold, the sign fixes this value. -/
def Completes (q : ℝ) (t : ℝ → Bool) : Prop :=
  ∀ θ, θ < |q| → (t θ = true ↔ 0 < q)

/-- Lemma 2.1(i). The two endpoint scores refer to the literals whose joint
truth violates the clause. -/
theorem completed_violation {α β u v : ℝ} (hα : 0 ≤ α) (hβ : α < β)
    (t s : ℝ → Bool) (ht : Completes u t) (hs : Completes v s) :
    chance α β {θ | t θ = true ∧ s θ = true ∧ (θ < |u| ∨ θ < |v|)} ≤
      ENNReal.ofReal (max (u + v) 0 / (β - α)) := by
  apply boundByInterval (lo := -(min u v)) (hi := max u v) hβ
  · rintro θ ⟨⟨hθα, _⟩, htθ, hsθ, ha⟩
    have hθ : 0 ≤ θ := hα.trans hθα
    have hu : θ < |u| → 0 < u := fun h => (ht θ h).mp htθ
    have hv : θ < |v| → 0 < v := fun h => (hs θ h).mp hsθ
    change -(min u v) ≤ θ ∧ θ < max u v
    simp only [abs_eq_max_neg, max_def, min_def] at *
    grind
  · rcases le_total u v with huv | hvu
    · rw [min_eq_left huv, max_eq_right huv]
      linarith [le_max_left (u + v) 0]
    · rw [min_eq_right hvu, max_eq_left hvu]
      linarith [le_max_left (u + v) 0]

/-- Exactly one endpoint is assigned, or both endpoints are assigned true. -/
def partialBad (u v : ℝ) : Set ℝ :=
  {θ | (θ < |u| ∧ |v| ≤ θ) ∨ (θ < |v| ∧ |u| ≤ θ) ∨
    (θ < |u| ∧ θ < |v| ∧ 0 < u ∧ 0 < v)}

/-- Lemma 2.1(ii). -/
theorem partial_violation {α β u v : ℝ} (hα : 0 ≤ α) (hβ : α < β) :
    chance α β (partialBad u v) ≤ ENNReal.ofReal (|u + v| / (β - α)) := by
  by_cases h : 0 < u ∧ 0 < v
  · obtain ⟨hu, hv⟩ := h
    apply boundByInterval (lo := 0) (hi := max u v) hβ
    · rintro θ ⟨⟨hθα, _⟩, he⟩
      change θ ∈ partialBad u v at he
      simp only [partialBad, Set.mem_ofPred_eq] at he
      simp only [abs_of_pos hu, abs_of_pos hv] at he
      refine ⟨hα.trans hθα, ?_⟩
      rcases he with he | he | he
      · exact lt_of_lt_of_le he.1 (le_max_left _ _)
      · exact lt_of_lt_of_le he.1 (le_max_right _ _)
      · exact lt_of_lt_of_le he.1 (le_max_left _ _)
    · rw [abs_of_pos (add_pos hu hv), sub_zero, max_le_iff]
      constructor <;> linarith
  · apply boundByInterval (lo := min |u| |v|) (hi := max |u| |v|) hβ
    · rintro θ ⟨_, he⟩
      change θ ∈ partialBad u v at he
      simp only [partialBad, Set.mem_ofPred_eq] at he
      change min |u| |v| ≤ θ ∧ θ < max |u| |v|
      rcases he with he | he | he <;> grind
    · simp only [abs_eq_max_neg, max_def, min_def]
      grind

end TwoSAT.Threshold

end

section

namespace TwoSAT.Cutoff

open Finset MeasureTheory TwoSAT.Threshold TwoSAT.Weights TwoSAT.ClauseLaw

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]

theorem measurable_bad (x y : ℝ) : MeasurableSet (partialBad x y) := by
  have h (a b : ℝ) : MeasurableSet {t : ℝ | t < |a| ∧ |b| ≤ t} :=
    measurableSet_Iio.inter measurableSet_Ici
  have last : MeasurableSet {t : ℝ | t < |x| ∧ t < |y| ∧ 0 < x ∧ 0 < y} := by
    exact (measurableSet_Iio (a := |x|)).inter
      ((measurableSet_Iio (a := |y|)).inter (MeasurableSet.const (0 < x ∧ 0 < y)))
  exact (h x y).union ((h y x).union last)

noncomputable def badMass (w x y : E → ℝ) (θ : ℝ) :=
  ∑ i, (partialBad (x i) (y i)).indicator (fun _ => w i) θ

/-- A single threshold controls all clauses, including those crossing the retained set. -/
theorem exists_threshold (w x y : E → ℝ) (hw : ∀ i, 0 ≤ w i) (sw : ∑ i, w i = 1)
    {scale : ℝ} (hscale : 0 < scale) :
    ∃ θ ∈ Set.Icc scale (2*scale), badMass w x y θ ≤ √(∑ i, w i * (x i+y i)^2) / scale := by
  let S := Set.Icc scale (2*scale)
  let μ : Measure ℝ := volume.restrict S
  let : IsFiniteMeasure μ := by dsimp [μ,S]; infer_instance
  have width : 2*scale - scale = scale := by ring
  have len : volume.real S = scale := by rw [Real.volume_real_Icc_of_le (by linarith : scale ≤ 2*scale),width]
  have fin : volume S ≠ ⊤ := measure_Icc_lt_top.ne
  have nonzero : volume S ≠ 0 := by
    intro hh
    have : volume.real S = 0 := by simp [measureReal_def,hh]
    linarith
  have hi (i : E) : Integrable ((partialBad (x i) (y i)).indicator (fun _ => w i)) μ :=
    (integrable_const _).indicator (measurable_bad ..)
  obtain ⟨θ,hθ,h⟩ := exists_le_setAverage nonzero fin (integrable_finsetSum univ (fun i _ => hi i))
  refine ⟨θ,hθ,h.trans ?_⟩
  rw [setAverage_eq,len,smul_eq_mul,← div_eq_inv_mul]
  apply div_le_div_of_nonneg_right _ hscale.le
  change (∫ θ, ∑ i, (partialBad (x i) (y i)).indicator (fun _ => w i) θ ∂μ) ≤ _
  rw [integral_finsetSum univ (fun i _ => hi i)]
  have one (i : E) : μ.real (partialBad (x i) (y i)) ≤ |x i+y i| := by
    have prob := partial_violation (u := x i) (v := y i) (α := scale) (β := 2*scale) hscale.le (by linarith)
    rw [chance,width] at prob
    have rr := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) prob
    rw [ENNReal.toReal_div,ENNReal.toReal_ofReal hscale.le,ENNReal.toReal_ofReal (div_nonneg (abs_nonneg _) hscale.le)] at rr
    apply (div_le_div_iff_of_pos_right hscale).mp
    simpa [μ,measureReal_def,Measure.restrict_apply (measurable_bad ..),Set.inter_comm,S] using rr
  have bound (i : E) : (∫ θ, (partialBad (x i) (y i)).indicator (fun _ => w i) θ ∂μ) ≤
        w i * |x i+y i| := by
    rw [integral_indicator (measurable_bad ..), setIntegral_const, smul_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (one i) (hw i)
  exact (sum_le_sum (s := univ) (fun i _ => bound i)).trans
    (TwoSAT.Reassignment.abs_average w (fun i => x i+y i) hw sw)

/-- Keep both endpoints in the small-score set, preserving the original weights. -/
noncomputable def internal (u v : E → Literal V) (w : E → ℝ) (q : Literal V → ℝ)
    (θ : ℝ) (i : E) :=
  if |q (u i)| ≤ θ ∧ |q (v i)| ≤ θ then w i else 0

noncomputable def extend (q : Literal V → ℝ) (θ : ℝ) (t : V → Bool) (x : V) : Bool :=
  if |q ⟨x,true⟩| ≤ θ then t x else decide (0 < q ⟨x,true⟩)

omit [Fintype V] [DecidableEq V] in
private theorem extend_spec (q : Literal V → ℝ) (anti : ∀ l, q l.flip = -q l) {θ : ℝ} (hθ : 0 ≤ θ)
    (t : V → Bool) (l : Literal V) :
    l.eval (extend q θ t) = (if |q l| ≤ θ then l.eval t else decide (0 < q l)) := by
  rcases l with ⟨x,b⟩
  have hf : q ⟨x,false⟩ = -q ⟨x,true⟩ := anti ⟨x,true⟩
  cases b <;> simp [Literal.eval,extend,hf]
  split_ifs at * <;> simp_all [abs_eq_max_neg,max_def]
  grind

omit [Fintype E] [Fintype V] [DecidableEq V] in
theorem cover (u v : E → Literal V) (w : E → ℝ) (hw : ∀ i, 0 ≤ w i)
    (q : Literal V → ℝ) (anti : ∀ l, q l.flip = -q l) {θ : ℝ} (hθ : 0 ≤ θ) (t : V → Bool) (i : E) :
    w i * charge 1 (extend q θ t) (u i) (v i) ≤ internal u v w q θ i * charge 1 t (u i) (v i) +
      (partialBad (q (u i)) (q (v i))).indicator (fun _ => w i) θ := by
  simp only [charge,extend_spec q anti hθ,internal, Set.indicator,partialBad, Set.mem_ofPred_eq]
  by_cases hu : |q (u i)| ≤ θ <;> by_cases hv : |q (v i)| ≤ θ <;>
    simp [hu,hv,lt_of_not_ge] <;> split_ifs at * <;> simp_all

omit [Fintype V] [DecidableEq V] in
/-- The loss part of Lemma 5.4. Every full assignment restricts to an assignment on
the retained variables, and any such restriction extends by the fixed outside values. -/
theorem internal_loss (u v : E → Literal V) (w : E → ℝ) (hw : ∀ i, 0 ≤ w i)
    (sw : ∑ i, w i = 1) (q : Literal V → ℝ) (anti : ∀ l, q l.flip = -q l) {δ scale : ℝ}
    (hscale : 0 < scale) (far : ∀ t, δ ≤ ∑ i, w i * charge 1 t (u i) (v i))
    (small : √(∑ i, w i * (q (u i)+q (v i))^2) / scale ≤ δ/2) :
    ∃ θ ∈ Set.Icc scale (2*scale), ∀ t, δ/2 ≤ ∑ i, internal u v w q θ i * charge 1 t (u i) (v i) := by
  obtain ⟨θ,hθ,h⟩ := exists_threshold w (fun i => q (u i)) (fun i => q (v i)) hw sw hscale
  refine ⟨θ,hθ,fun t => ?_⟩
  have hh := (far (extend q θ t)).trans (sum_le_sum (s := univ) (fun i _ =>
    cover u v w hw q anti (hscale.le.trans hθ.1) t i))
  rw [sum_add_distrib] at hh
  unfold badMass at h
  linarith only [hh,h,small]

/-- Counting both incident literals bounds the total weight of internal clauses. -/
theorem internal_mass (u v : E → Literal V) (w : E → ℝ) (hw : ∀ i, 0 ≤ w i)
    (q : Literal V → ℝ) (θ : ℝ) :
    (∑ i, internal u v w q θ i) ≤ ∑ l, seed u v w l * (if |q l| ≤ θ then 1 else 0) := by
  rw [TwoSAT.Balance.seed_integral]
  rw [sum_div]
  apply sum_le_sum; intro i _
  unfold internal
  split_ifs <;> grind [hw i]

omit [DecidableEq V] in
/-- Equation (31), for any nonnegative affinity function and its complementary difference. -/
theorem retained_affinity (μ a : Literal V → ℝ) (hμ : ∀ l, 0 ≤ μ l)
    (hs : ∑ l, μ l = 1) (ha : ∀ l, 0 ≤ a l) {θ scale : ℝ} (hθ : θ ≤ 2*scale)
    (hscale : 0 ≤ scale) :
    (∑ l, μ l * (if |a l.flip-a l| ≤ θ then a l else 0)) ≤
      2*scale + ∑ l, μ l * min (a l) (a l.flip) := by
  rw [← one_mul (2*scale),← hs,sum_mul,← sum_add_distrib]
  apply sum_le_sum; intro l _
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (hμ l)
  split_ifs with h
  · have := (abs_le.mp h).1
    grind
  · exact add_nonneg (by positivity) (le_min (ha l) (ha l.flip))

/-- The complement-closed cutoff of Lemma 5.4 with its original internal weights. -/
theorem balanced_cutoff (u v : E → Literal V) (w : E → ℝ) (hw : ∀ i, 0 ≤ w i)
    (sw : ∑ i, w i = 1) (bal : ∀ x, imbalance u v w x = 0)
    {δ η scale : ℝ} (hη : 0 < η) (half : η ≤ 1/2) (hscale : 0 < scale)
    (err : √(32*η)/scale ≤ δ/2) (far : ∀ t, δ ≤ ∑ i, w i * charge 1 t (u i) (v i)) :
    let a := (forward u v w hw).lazy.endpointAffinity η flipPerm
    let q := fun l : Literal V => a l.flip-a l
    let μ := seed u v w
    ∃ θ ∈ Set.Icc scale (2*scale),
      (∀ t, δ/2 ≤ ∑ i, internal u v w q θ i * charge 1 t (u i) (v i)) ∧
      δ/2 ≤ ∑ l, μ l * (if |q l| ≤ θ then 1 else 0) ∧
      (∑ l, μ l * (if |q l| ≤ θ then a l else 0)) ≤
        2*scale + ∑ l, μ l * min (a l) (a l.flip) := by
  obtain ⟨anti,energy⟩ := affinity_difference u v w hw sw bal hη half
  let a := (forward u v w hw).lazy.endpointAffinity η flipPerm
  let q := fun l : Literal V => a l.flip-a l
  obtain ⟨θ,hθ,loss⟩ := internal_loss u v w hw sw q anti hscale far
    ((div_le_div_of_nonneg_right (Real.sqrt_le_sqrt energy) hscale.le).trans err)
  refine ⟨θ,hθ,loss,(loss (fun _ => false)).trans (le_trans ?_ (internal_mass u v w hw q θ)),?_⟩
  · apply sum_le_sum; intro i _; unfold internal charge; split_ifs <;> simp [hw]
  · exact retained_affinity _ a (seed_nonneg u v hw) ((seed_total u v w).trans sw)
      (fun l => ((forward u v w hw).lazy.affinity_bounds hη (by linarith) flipPerm l).1) hθ.2 hscale.le

end TwoSAT.Cutoff

end

section

namespace TwoSAT.ColumnRounding

open Finset TwoSAT.Walk TwoSAT.Entropy TwoSAT.Weights TwoSAT.ClauseLaw

variable {V E S : Type} [Fintype V] [DecidableEq V] [Fintype E] [Fintype S]

theorem variation_bound (p q : S → ℝ) (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (sp : ∑ s, p s = 1) (sq : ∑ s, q s = 1) {t : ℝ} (ht : 0 < t) :
    (∑ s, |p s-q s|) ≤ t+(∑ s, (√(p s)-√(q s))^2)/t := by
  have pt (s : S) : |p s-q s| ≤ (t/2)*(p s+q s) + (√(p s)-√(q s))^2/t := by
    let x := √(p s)
    let y := √(q s)
    have hx : x^2 = p s := Real.sq_sqrt (hp s)
    have hy : y^2 = q s := Real.sq_sqrt (hq s)
    have factor : |p s-q s| = |x-y| *(x+y) := by
      rw [← hx,← hy,sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      exact mul_comm ..
    rw [factor]
    apply (mul_le_mul_iff_of_pos_right ht).mp
    rw [add_mul,div_mul_cancel₀ _ ht.ne']
    change _ ≤ _ + (x-y)^2
    nlinarith only [sq_nonneg (|x-y| - t*(x+y)/2),sq_abs (x-y),
      mul_nonneg (sq_nonneg t) (sq_nonneg (x-y)),congrArg (fun z => t^2*z) hx,congrArg (fun z => t^2*z) hy]
  have h := sum_le_sum (s := univ) (fun s _ => pt s)
  rw [sum_add_distrib,← mul_sum,sum_add_distrib,sp,sq,← sum_div] at h
  linarith only [h]

/-- The rounding loss for the retained clauses in terms of affinity and the full walk energy. -/
theorem retained_rounding (u v : E → Literal V) (w : E → ℝ) (hw : ∀ i, 0 ≤ w i)
    (sw : ∑ i, w i = 1) (keep : Literal V → Bool) (p : Literal V → S → ℝ)
    (hp : ∀ i l, 0 ≤ p i l) (sp : ∀ i, ∑ l, p i l = 1) {δ t : ℝ} (ht : 0 < t)
    (far : ∀ a, δ ≤ ∑ i, (if keep (u i) && keep (v i) then w i else 0) * charge 1 a (u i) (v i)) :
    2*δ ≤ 4*(∑ i, seed u v w i * (if keep i then affinity (p i) (p i.flip) else 0)) +
      2*t + (2/t)*∑ l, (forward u v w hw).energy (seed u v w) (fun i => √(p i l)) := by
  let z i := if keep (u i) && keep (v i) then w i else 0
  have hz (i) : 0 ≤ z i := by dsimp [z]; split_ifs <;> simp [hw]
  have round := round_columns u v z hz p hp sp far
  let c (i : Literal V) := affinity (p i) (p i.flip)
  let a (i : Literal V) := if keep i then c i else 0
  let g (i j : Literal V) := ∑ l, (√(p i l)-√(p j l))^2
  let d (i j : Literal V) := ∑ l, |p i l-p j l|
  have hc (i : Literal V) : 0 ≤ c i := sum_nonneg fun l _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hg (i j : Literal V) : 0 ≤ g i j := sum_nonneg fun l _ => sq_nonneg _
  have hd (i j : Literal V) : d i j ≤ t+g i j/t := variation_bound _ _ (hp i) (hp j) (sp i) (sp j) ht
  have ha (i) : 0 ≤ a i := by dsimp [a]; split_ifs <;> simp [hc]
  have pt (i : E) : z i * (2*c (u i)+(d (u i) (v i).flip+d (v i) (u i).flip)) ≤
      2*(w i*(a (u i)+a (v i))) + (2*t)*w i +
      (2/t)*((w i/2)*(g (u i) (v i).flip+g (v i) (u i).flip)) := by
    by_cases h : (keep (u i) && keep (v i)) = true
    · obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp h
      change (if (keep (u i) && keep (v i)) = true then w i else 0)*_ ≤ _
      rw [if_pos h]; simp only [a,h1,h2,if_true]
      have hsum := add_le_add (hd (u i) (v i).flip) (hd (v i) (u i).flip)
      apply (mul_le_mul_of_nonneg_left (add_le_add_right hsum (2*c (u i))) (hw i)).trans
      have hn := mul_nonneg (hw i) (hc (v i))
      simp only [div_eq_mul_inv]; linarith only [hn]
    · have hz0 : z i = 0 := if_neg h
      rw [hz0,zero_mul]
      exact add_nonneg (add_nonneg (mul_nonneg (by norm_num) (mul_nonneg (hw i) (add_nonneg (ha _) (ha _)))) (mul_nonneg (by positivity) (hw i))) (mul_nonneg (by positivity) (mul_nonneg (div_nonneg (hw i) (by norm_num)) (add_nonneg (hg ..) (hg ..))))
  have h := sum_le_sum (s := univ) (fun i _ => pt i)
  simp only [sum_add_distrib] at round
  have rh := round.trans h
  rw [sum_add_distrib,sum_add_distrib,← mul_sum,← mul_sum,sw,mul_one,← mul_sum] at rh
  have seedmean := TwoSAT.Balance.seed_integral u v w a
  rw [← arc_integral u v w hw g] at rh
  have energy (i : Literal V) : (∑ j, (forward u v w hw).prob i j*g i j) =
      ∑ l, ∑ j, (forward u v w hw).prob i j*(√(p i l)-√(p j l))^2 := by
    simp only [g,mul_sum]; rw [sum_comm]
  have exchange : (∑ i, seed u v w i * ∑ j, (forward u v w hw).prob i j*g i j) =
      ∑ l, (forward u v w hw).energy (seed u v w) (fun i => √(p i l)) := by
    simp only [energy,Kernel.energy]
    conv_lhs => enter [2,i]; rw [mul_sum]
    rw [sum_comm]
  rw [exchange] at rh
  change 2*δ ≤ 4*(∑ i, seed u v w i*a i) + 2*t +
    (2/t)*∑ l, (forward u v w hw).energy (seed u v w) (fun i => √(p i l))
  linarith only [rh,seedmean]

end TwoSAT.ColumnRounding

end

section

namespace TwoSAT.Entropy

theorem rel_sqrt_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 < a → 0 < b) :
    (√a - √b)^2 ≤ rel a b - a + b := by
  rcases ha.eq_or_lt with h | h
  · rw [← h]; simp [rel,Real.sq_sqrt hb]
  have hp := hs h
  let x := √a
  let y := √b
  have hx : 0 < x := Real.sqrt_pos.mpr h
  have hy : 0 < y := Real.sqrt_pos.mpr hp
  have xa : x^2 = a := Real.sq_sqrt ha
  have yb : y^2 = b := Real.sq_sqrt hb
  have logeq : Real.log (a/b) = 2 * Real.log (x/y) := by rw [← xa, ← yb, ← div_pow, Real.log_pow]; norm_num
  have hh := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos (div_pos hx hy)) (show 0 ≤ 2*x^2 by positivity)
  have eq : 2*x^2 * (1-(x/y)⁻¹) = 2*x^2-2*x*y := by rw [inv_div]; field_simp
  rw [eq] at hh
  change (x-y)^2 ≤ a * Real.log (a/b) - a + b
  rw [logeq, ← xa, ← yb]
  linarith only [hh]

/-- Natural-log entropy dissipation for the lazy average. -/
theorem lazy_entropy_gap {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (√a - √b)^2 / 2 ≤ rel a ((a+b)/2) + rel b ((a+b)/2) := by
  let m := (a+b)/2
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have h1 := rel_sqrt_bound ha hm (fun h => by dsimp [m]; linarith)
  have h2 := rel_sqrt_bound hb hm (fun h => by dsimp [m]; linarith)
  change _ ≤ rel a m + rel b m
  have he : 2*m = a+b := by dsimp [m]; ring
  nlinarith only [h1, h2, he, sq_nonneg (√a+√b-2*√m)]

end TwoSAT.Entropy

end

section

namespace TwoSAT.Walk.Kernel

open Finset TwoSAT.Entropy TwoSAT.ClauseLaw

variable {S : Type} [Fintype S] [DecidableEq S]

theorem steps_last (K : Kernel S) (r : ℕ) (s t : S) :
    K.steps (r+1) s t = ∑ i, K.steps r s i * K.prob i t := by
  induction r generalizing s with
  | zero => simp [steps,ite_mul,mul_ite]
  | succ r ih =>
    change (∑ i, K.prob s i * K.steps (r+1) i t) = _
    conv_lhs => simp only [ih,mul_sum]
    simp only [steps,sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intros; ring

/-- Conditioning on the final step, in the row-vector convention. -/
theorem endpoint_last (K : Kernel S) {η : ℝ} (hη : 0 < η) (hu : η < 1) (s t : S) :
    K.endpoint η s t = η*(if s=t then 1 else 0) +
      (1-η)* ∑ i, K.endpoint η s i * K.prob i t := by
  have expand (r : ℕ) : (1-η)^(r+1) * K.steps (r+1) s t =
      ∑ i, ((1-η)*K.prob i t) * ((1-η)^r * K.steps r s i) := by
    rw [K.steps_last,pow_succ,mul_sum]; apply sum_congr rfl; intros; ring
  rw [endpoint,(K.summable_steps hη hu s t).tsum_eq_zero_add]
  simp only [pow_zero,one_mul,show K.steps 0 s t = (if s=t then 1 else 0) from rfl]
  simp_rw [expand]
  rw [Summable.tsum_finsetSum (fun i (_ : i ∈ univ) =>
    (K.summable_steps hη hu s i).mul_left ((1-η)*K.prob i t))]
  simp only [tsum_mul_left,endpoint,mul_add,mul_sum]
  congr 1; apply sum_congr rfl; intros; ring

noncomputable def advance (K : Kernel S) (m : S → ℝ) (j : S) := ∑ i, m i*K.prob i j

omit [DecidableEq S] in
theorem advance_nonneg (K : Kernel S) {m : S → ℝ} (hm : ∀ i, 0 ≤ m i) (j) : 0 ≤ K.advance m j :=
  sum_nonneg fun i _ => mul_nonneg (hm i) (K.nonneg ..)

omit [DecidableEq S] in
theorem advance_sum (K : Kernel S) (m : S → ℝ) : ∑ j, K.advance m j = ∑ i, m i := by
  unfold advance; rw [sum_comm]; simp [← mul_sum,K.row]

private theorem marginal_snd (a : S × S → ℝ) (j : S) :
    mass Prod.snd a j = ∑ i, a (i,j) := by simp [mass,Fintype.sum_prod_type]

theorem rel_density (q x : ℝ) (hq : 0 ≤ q) (_hx : 0 ≤ x) :
    rel (q*x) q = q*(x*Real.log x) := by
  rcases hq.eq_or_lt with hz | hq
  · simp [← hz,rel]
  · simp [rel,hq.ne',mul_assoc]

/-- An entropy decrease across one lazy step controls the Dirichlet energy of the
square-root density. The factor 1/4 uses natural logarithms. -/
theorem entropy_drop (J : Kernel S) (μ f : S → ℝ) (hp : ∀ i, 0 ≤ μ i)
    (stat : J.Stationary μ) (hf : ∀ i, 0 ≤ f i) :
    J.energy μ (fun i => √(f i)) / 4 ≤
      divergence (fun i => μ i*f i) μ - divergence (J.lazy.advance (fun i => μ i*f i)) μ := by
  let q (x : S × S) := μ x.1 * J.prob x.1 x.2
  let mid (x : S × S) := (f x.1 + f x.2)/2
  let ψ (z : ℝ) := z*Real.log z
  have hq (x) : 0 ≤ q x := mul_nonneg (hp _) (J.nonneg ..)
  have hm (x) : 0 ≤ mid x := div_nonneg (add_nonneg (hf _) (hf _)) (by norm_num)
  have D := data_processing Prod.snd (fun x => q x*mid x) q
    (fun x => mul_nonneg (hq x) (hm x)) hq (fun x h => pos_of_mul_pos_left h (hm x))
  have orig : mass Prod.snd q = μ := by funext j; rw [marginal_snd]; exact stat j
  have dest : mass Prod.snd (fun x => q x*mid x) = J.lazy.advance (fun i => μ i*f i) := by
    funext j
    rw [marginal_snd]
    have eq (i : S) : q (i,j)*mid (i,j) =
        (μ i*f i*J.prob i j + μ i*J.prob i j*f j)/2 := by dsimp [q,mid]; ring
    simp only [eq,← sum_div,sum_add_distrib,← sum_mul,stat j,advance,lazy,mul_add,
      mul_ite,mul_zero,sum_ite_eq',mem_univ,if_true]
    have half (i : S) : μ i*f i*(1/2*J.prob i j) = (μ i*f i*J.prob i j)/2 := by ring
    simp only [half,← sum_div]; ring
  rw [orig,dest] at D
  have massψ (x : S × S) : rel (q x*mid x) (q x) = q x*ψ (mid x) :=
    rel_density _ _ (hq x) (hm x)
  change _ ≤ ∑ x, rel _ _ at D
  simp only [massψ] at D
  have marginals (g : S → ℝ) : (∑ x, q x*(g x.1 + g x.2)) = 2*∑ i, μ i*g i := by
    simp only [q,Fintype.sum_prod_type,mul_add,sum_add_distrib]
    have left (s : S) : ∑ j, μ s*J.prob s j*g s = μ s*g s := by
      rw [← sum_mul,← mul_sum,J.row,mul_one]
    simp only [left]
    simp only [mul_assoc,← mul_sum,J.stationary_mean stat]
    ring
  have gap (i j : S) : (√(f i)-√(f j))^2/2 ≤ ψ (f i) + ψ (f j) - 2*ψ (mid (i,j)) := by
    have rewriteRel (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
        rel a ((a+b)/2) = ψ a - a*Real.log ((a+b)/2) := by
      rcases ha.eq_or_lt with hz | ha
      · simp [← hz,rel,ψ]
      · simp [rel,ψ,Real.log_div ha.ne' (show 0 < (a+b)/2 by positivity).ne',mul_sub]
    have hh := lazy_entropy_gap (hf i) (hf j)
    rw [rewriteRel _ _ (hf i) (hf j),add_comm (f i) (f j),rewriteRel _ _ (hf j) (hf i),
      add_comm (f j) (f i)] at hh
    dsimp only [ψ,mid] at *
    linarith only [hh]
  have H := sum_le_sum (s := (univ : Finset (S × S))) (fun x _ =>
    mul_le_mul_of_nonneg_left (gap x.1 x.2) (hq x))
  have energy_eq : ∑ x : S × S, q x * ((√(f x.1)-√(f x.2))^2/2) = J.energy μ (fun i => √(f i))/2 := by
    simp [q,energy,Fintype.sum_prod_type,mul_sum,sum_div]; apply sum_congr rfl; intros
    apply sum_congr rfl; intros; ring
  have linear (x : S × S) : q x*(ψ (f x.1)+ψ (f x.2)-2*ψ (mid x)) =
      q x*(ψ (f x.1)+ψ (f x.2)) - 2*(q x*ψ (mid x)) := by ring
  simp only [energy_eq,linear,sum_sub_distrib,← mul_sum] at H
  rw [marginals (fun i => ψ (f i))] at H
  have base : divergence (fun i => μ i*f i) μ = ∑ i, μ i*ψ (f i) := by
    apply sum_congr rfl; intro i _; exact rel_density _ _ (hp i) (hf i)
  linarith only [D,H,base]

end TwoSAT.Walk.Kernel

end

section

namespace TwoSAT.Walk.Kernel

open Finset

variable {S : Type} [Fintype S] [DecidableEq S]

/-- Reverse the chain on the stationary support, with holding at zero-mass states. -/
noncomputable def reverse (K : Kernel S) (μ : S → ℝ) (hp : ∀ i, 0 ≤ μ i)
    (stat : K.Stationary μ) : Kernel S where
  prob i j := if μ i = 0 then (if i=j then 1 else 0) else (μ j*K.prob j i)/μ i
  nonneg i j := by split_ifs <;> first | positivity | exact div_nonneg (mul_nonneg (hp j) (K.nonneg ..)) (hp i)
  row i := by
    by_cases hz : μ i = 0
    · simp [hz]
    · simp only [hz,if_false,← sum_div,stat i,div_self hz]

theorem reverse_flow (K : Kernel S) (μ : S → ℝ) (hp : ∀ i, 0 ≤ μ i)
    (stat : K.Stationary μ) (i j : S) :
    μ i * (K.reverse μ hp stat).prob i j = μ j*K.prob j i := by
  by_cases h : μ i = 0
  · have hb := single_le_sum (s := univ) (fun k _ => mul_nonneg (hp k) (K.nonneg k i)) (mem_univ j)
    rw [stat i,h] at hb
    simpa only [h,zero_mul] using hb.antisymm (mul_nonneg (hp j) (K.nonneg j i)) |>.symm
  · simp [reverse,h,mul_div_cancel₀]

/-- The second copy of the state space records the most recent refreshed label. -/
noncomputable def marked (K : Kernel S) (b : S → ℝ) (hb : ∀ i, 0 ≤ b i) (hu : ∀ i, b i ≤ 1) :
    Kernel (S ⊕ S) where
  prob := fun i j => match i,j with
    | .inl s,.inl t => (1-b s)*K.prob s t
    | .inl s,.inr t => if t=s then b s else 0
    | .inr _,.inl _ => 0
    | .inr s,.inr t => if t=s then 1 else 0
  nonneg := by
    rintro (s|s) (t|t)
    · exact mul_nonneg (sub_nonneg.mpr (hu s)) (K.nonneg s t)
    · change 0 ≤ if t=s then b s else 0
      split_ifs <;> simp [hb]
    · rfl
    · change 0 ≤ if t=s then (1:ℝ) else 0
      split_ifs <;> norm_num
  row := by
    rintro (s|s) <;> simp [Fintype.sum_sum_type,← mul_sum,K.row]

private theorem absorbing (K : Kernel S) (b : S → ℝ) (hb : ∀ i, 0 ≤ b i) (hu : ∀ i, b i ≤ 1) {η : ℝ} (hη : 0 < η) (h1 : η < 1)
    (s : S) (t : S ⊕ S) :
    (K.marked b hb hu).endpoint η (.inr s) t = if Sum.inr s=t then 1 else 0 := by
  have h := (K.marked b hb hu).endpoint_rec hη h1 (.inr s) t
  simp only [Fintype.sum_sum_type,marked,zero_mul,sum_const_zero,zero_add,ite_mul,one_mul,
    sum_ite_eq',mem_univ,if_true] at h
  change (K.marked b hb hu).endpoint η (.inr s) t =
    η*(if Sum.inr s=t then 1 else 0)+(1-η)*(K.marked b hb hu).endpoint η (.inr s) t at h
  have he : η*((K.marked b hb hu).endpoint η (.inr s) t - (if Sum.inr s=t then 1 else 0)) = 0 := by linarith only [h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hη.ne')

/-- At a geometric time report the refreshed label, or none while the chain is still moving. -/
noncomputable def labels (K : Kernel S) (b : S → ℝ) (hb : ∀ i, 0 ≤ b i) (hu : ∀ i, b i ≤ 1) (η : ℝ) (i : S) : Option S → ℝ
  | none => ∑ j, (K.marked b hb hu).endpoint η (.inl i) (.inl j)
  | some j => (K.marked b hb hu).endpoint η (.inl i) (.inr j)

theorem labels_nonneg (K : Kernel S) (b : S → ℝ) (hb : ∀ i, 0 ≤ b i) (hu : ∀ i, b i ≤ 1) {η : ℝ} (hη : 0 < η) (h1 : η < 1)
    (i : S) (l : Option S) : 0 ≤ K.labels b hb hu η i l := by
  cases l
  · exact sum_nonneg fun _ _ => (K.marked b hb hu).endpoint_nonneg hη h1 .. 
  · exact (K.marked b hb hu).endpoint_nonneg hη h1 ..

theorem labels_sum (K : Kernel S) (b : S → ℝ) (hb : ∀ i, 0 ≤ b i) (hu : ∀ i, b i ≤ 1) {η : ℝ} (hη : 0 < η) (h1 : η < 1)
    (i : S) : ∑ l, K.labels b hb hu η i l = 1 := by
  simpa only [Fintype.sum_option,labels,Fintype.sum_sum_type] using (K.marked b hb hu).endpoint_row hη h1 (.inl i)

theorem labels_rec (K : Kernel S) (b : S → ℝ) (hb : ∀ i, 0 ≤ b i) (hu : ∀ i, b i ≤ 1) {η : ℝ} (hη : 0 < η) (h1 : η < 1)
    (i : S) (l : Option S) :
    K.labels b hb hu η i l =
      η*(if l=none then 1 else 0) + (1-η)*(b i*(if l=some i then 1 else 0) +
        (1-b i)*∑ j, K.prob i j * K.labels b hb hu η j l) := by
  let A := K.marked b hb hu
  have step (t : S ⊕ S) : A.endpoint η (.inl i) t =
      η*(if Sum.inl i=t then 1 else 0) + (1-η)*(b i*(if Sum.inr i=t then 1 else 0) +
        (1-b i)*∑ j, K.prob i j*A.endpoint η (.inl j) t) := by
    rw [A.endpoint_rec hη h1]
    congr 2
    rw [Fintype.sum_sum_type]
    change (∑ j, (1-b i)*K.prob i j*A.endpoint η (.inl j) t) +
      (∑ j, (if j=i then b i else 0)*A.endpoint η (.inr j) t) = _
    simp only [ite_mul,zero_mul,sum_ite_eq',mem_univ,if_true,mul_assoc,← mul_sum]
    rw [show A.endpoint η (.inr i) t = _ from absorbing K b hb hu hη h1 i t,add_comm]
  cases l with
  | some s =>
    simpa [labels,A,eq_comm] using step (.inr s)
  | none =>
    simp only [labels]
    change (∑ j, A.endpoint η (.inl i) (.inl j)) = _
    conv_lhs => enter [2,j]; rw [step]
    simp only [Sum.inl.injEq,Sum.inr_ne_inl,if_false,mul_zero,zero_add,sum_add_distrib,
      ← mul_sum,sum_ite_eq,mem_univ,if_true,show (none : Option S) ≠ some i by simp,mul_one]
    congr 2
    rw [sum_comm]
    simp only [← mul_sum,A]

end TwoSAT.Walk.Kernel

end

section

namespace TwoSAT.Walk.Kernel

open Finset

variable {S : Type} [Fintype S] [DecidableEq S]

noncomputable def average (K : Kernel S) (f : S → ℝ) (i : S) := ∑ j, K.prob i j * f j

omit [DecidableEq S] in
theorem average_nonneg (K : Kernel S) {f : S → ℝ} (hf : ∀ i, 0 ≤ f i) (i : S) :
    0 ≤ K.average f i := sum_nonneg fun j _ => mul_nonneg (K.nonneg ..) (hf j)

theorem reverse_average (K : Kernel S) (μ : S → ℝ) (hp : ∀ i, 0 ≤ μ i) (stat : K.Stationary μ)
    (f : S → ℝ) (i : S) : μ i * (K.reverse μ hp stat).average f i =
      K.advance (fun j => μ j*f j) i := by
  simp only [average,mul_sum,← mul_assoc,K.reverse_flow μ hp stat,advance]
  apply sum_congr rfl; intros; ring

omit [DecidableEq S] in
/-- A strict contraction of a nonnegative mass cannot have a positive subsolution. -/
theorem advance_comparison (K : Kernel S) (x y : S → ℝ) {r : ℝ} (hr : 0 ≤ r) (hu : r < 1)
    (h : ∀ i, x i-y i ≤ r*K.advance (fun j => x j-y j) i) (i : S) : x i ≤ y i := by
  let f j := max (x j-y j) 0
  have hf (j : S) : 0 ≤ f j := le_max_right .. 
  have leq (j : S) : f j ≤ r*K.advance f j := by
    apply max_le _ (mul_nonneg hr (K.advance_nonneg hf j))
    apply (h j).trans (mul_le_mul_of_nonneg_left _ hr)
    exact sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (le_max_left ..) (K.nonneg k j)
  have hh := sum_le_sum (s := univ) (fun j _ => leq j)
  rw [← mul_sum,K.advance_sum] at hh
  have hn : ∑ j, f j ≤ 0 := by nlinarith only [hh,hu]
  have hs := (single_le_sum (s := univ) (fun j _ => hf j) (mem_univ i)).trans hn
  linarith only [(le_max_left (x i-y i) 0).trans hs]

theorem label_endpoint_bound (K : Kernel S) (μ : S → ℝ) (hp : ∀ i, 0 ≤ μ i)
    (stat : K.Stationary μ) (b : S → ℝ) (hb : ∀ i, 0 ≤ b i) (hu : ∀ i, b i ≤ 1)
    {η : ℝ} (hη : 0 < η) (h1 : η < 1) (s i : S) :
    μ i * (K.reverse μ hp stat).labels b hb hu η i (some s) ≤
      (μ s * b s / η)*K.endpoint η s i := by
  let B := K.reverse μ hp stat
  let p j := B.labels b hb hu η j (some s)
  let c := μ s*b s/η
  let x j := μ j*p j
  let y j := c*K.endpoint η s j
  have hr : 0 ≤ 1-η := sub_nonneg.mpr h1.le
  have hrec (j : S) := B.labels_rec b hb hu hη h1 j (some s)
  have sub (j : S) : x j ≤ μ j*b j*(if s=j then 1 else 0) + (1-η)*K.advance x j := by
    have pos := B.average_nonneg (fun k => B.labels_nonneg b hb hu hη h1 k (some s)) j
    have eqn : p j = (1-η)*(b j*(if s=j then 1 else 0)+(1-b j)*B.average p j) := by
      simpa [p,average] using hrec j
    have h := K.reverse_average μ hp stat p j
    change μ j*B.average p j = K.advance x j at h
    rw [← h]; dsimp only [x]; rw [eqn]
    have small : (1-η)*((1-b j)*B.average p j) ≤ (1-η)*B.average p j :=
      mul_le_mul_of_nonneg_left (mul_le_of_le_one_left pos (by linarith [hb j])) hr
    by_cases e : s=j <;> simp only [e,if_true,if_false,mul_one,mul_zero,zero_add] at *
    · nlinarith only [mul_le_mul_of_nonneg_left small (hp j),mul_nonneg hη.le (mul_nonneg (hp j) (hb j))]
    · linarith only [mul_le_mul_of_nonneg_left small (hp j)]
  have eqy (j : S) : y j = μ j*b j*(if s=j then 1 else 0) + (1-η)*K.advance y j := by
    have ce : c*η = μ s*b s := div_mul_cancel₀ _ hη.ne'
    change c*K.endpoint η s j = _
    rw [K.endpoint_last hη h1]
    simp only [advance,y,mul_assoc,← mul_sum]
    by_cases h : s=j <;> simp only [h,if_true,if_false,mul_one,mul_zero,zero_add] at * <;>
      linarith only [ce]
  apply K.advance_comparison x y hr (by linarith) _ i
  intro j
  have linear : K.advance (fun k => x k-y k) j = K.advance x j-K.advance y j := by
    simp only [advance,sub_mul,sum_sub_distrib]
  rw [linear]
  linarith only [sub j,eqy j]

end TwoSAT.Walk.Kernel

end

section

namespace TwoSAT.RefreshEntropy

open Finset TwoSAT.Entropy TwoSAT.Walk

variable {L S : Type} [Fintype L] [Fintype S] [DecidableEq S]

noncomputable def negEntropy (p : L → ℝ) := ∑ l, p l * Real.log (p l)

theorem lower_entropy (p : L → ℝ) (hp : ∀ l, 0 ≤ p l) (sp : ∑ l, p l = 1) :
    -Real.log (Fintype.card L) ≤ negEntropy p := by
  have h := log_sum p (fun _ => 1) hp (fun _ => zero_le_one) (fun _ _ => zero_lt_one)
  simpa [rel,sp,negEntropy,one_div] using h

theorem mix_entropy (p q : L → ℝ) (hp : ∀ l, 0 ≤ p l) (hq : ∀ l, 0 ≤ q l)
    {a : ℝ} (ha : 0 ≤ a) (hu : a ≤ 1) :
    negEntropy (fun l => a*p l + (1-a)*q l) ≤ a*negEntropy p + (1-a)*negEntropy q := by
  simp only [negEntropy,mul_sum,← sum_add_distrib]
  exact sum_le_sum fun l _ => Real.convexOn_mul_log.2 (hp l) (hq l) ha (sub_nonneg.mpr hu) (by ring)

theorem atom_mix [DecidableEq L] (j : L) (q : L → ℝ) (hq : ∀ l, 0 ≤ q l)
    {a : ℝ} (ha : 0 ≤ a) (hu : a ≤ 1) :
    negEntropy (fun l => a*(if l=j then 1 else 0) + (1-a)*q l) ≤ (1-a)*negEntropy q := by
  let d (l : L) : ℝ := if l=j then 1 else 0
  have hd (l) : 0 ≤ d l := by dsimp [d]; split_ifs <;> norm_num
  have he : negEntropy d = 0 := by
    unfold negEntropy
    apply sum_eq_zero; intro l _; dsimp [d]; split_ifs <;> simp
  simpa only [he,mul_zero,zero_add] using mix_entropy d q hd hq ha hu

/-- Entropy inserted by a refresh at a state costs at most its refresh probability times log |L|. -/
theorem refresh_gap (p q : Option S → ℝ) (hq : ∀ l, 0 ≤ q l) (sq : ∑ l, q l = 1)
    (i : S) {η b : ℝ} (hη : 0 ≤ η) (hu : η ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (h : ∀ l, p l = η*(if l=none then 1 else 0) +
        (1-η)*(b*(if l=some i then 1 else 0)+(1-b)*q l)) :
    negEntropy p - negEntropy q ≤ (η+b)*Real.log (Fintype.card (Option S)) := by
  let r l := b*(if l=some i then 1 else 0)+(1-b)*q l
  have hr (l) : 0 ≤ r l := by
    dsimp [r]; split_ifs <;> simp [add_nonneg,hb,mul_nonneg (sub_nonneg.mpr hb1) (hq l)]
  have mix := atom_mix none r hr hη hu
  rw [← funext h] at mix
  have small := atom_mix (some i) q hq hb hb1
  change negEntropy r ≤ _ at small
  have lower := lower_entropy q hq sq
  have logpos : 0 ≤ Real.log (Fintype.card (Option S)) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Option S)) |> Nat.succ_le_of_lt)
  have coeff : 0 ≤ η+b-η*b := by nlinarith [mul_nonneg (sub_nonneg.mpr hu) hb]
  nlinarith only [mix,mul_le_mul_of_nonneg_left small (sub_nonneg.mpr hu),
    mul_le_mul_of_nonneg_left lower coeff,mul_nonneg (mul_nonneg hη hb) logpos]

theorem collected_energy (J : Kernel S) (μ : S → ℝ) (hp : ∀ i, 0 ≤ μ i)
    (stat : J.Stationary μ) (p q : S → L → ℝ) (hn : ∀ i l, 0 ≤ p i l) (hq : ∀ i l, 0 ≤ q i l)
    (flow : ∀ i l, μ i*q i l = J.lazy.advance (fun j => μ j*p j l) i) :
    (∑ l, J.energy μ (fun i => √(p i l))) ≤
       4*(∑ i, μ i*(negEntropy (p i) - negEntropy (q i))) := by
  have one (l : L) := Kernel.entropy_drop J μ (fun i => p i l) hp stat (fun i => hn i l)
  have expand (f : S → ℝ) (hf : ∀ i, 0 ≤ f i) : divergence (fun i => μ i*f i) μ =
      ∑ i, μ i*(f i*Real.log (f i)) := by
    exact sum_congr rfl (fun i _ => Kernel.rel_density _ _ (hp i) (hf i))
  have hh (l : L) := one l
  have right (l : L) : J.lazy.advance (fun j => μ j*p j l) = fun i => μ i*q i l := funext fun i => (flow i l).symm
  simp only [right,expand _ (fun i => hn i _),expand _ (fun i => hq i _)] at hh
  have h := sum_le_sum (s := univ) (fun l _ => hh l)
  simp only [← sum_div,← sum_sub_distrib] at h
  rw [sum_comm (f := fun l i => μ i*(p i l*Real.log (p i l))-μ i*(q i l*Real.log (q i l)))] at h
  simp only [← mul_sub,← mul_sum,sum_sub_distrib] at h
  dsimp only [negEntropy]; linarith only [h]

end TwoSAT.RefreshEntropy

end

section

namespace TwoSAT.Walk.Kernel

open Finset TwoSAT.RefreshEntropy

variable {S : Type} [Fintype S] [DecidableEq S]

/-- Stationary endpoint columns with labels refreshed at the chosen states. The distinguished
empty label accounts for paths stopped before their first refresh. -/
theorem localized_labels (J : Kernel S) (μ : S → ℝ) (hp : ∀ i, 0 ≤ μ i) (hs : ∑ i, μ i = 1)
    (stat : J.Stationary μ) (b : S → ℝ) {κ η : ℝ} (hb : ∀ i, 0 ≤ b i) (hκ : κ ≤ 1)
    (bound : ∀ i, b i ≤ κ) (hη : 0 < η) (h1 : η < 1) :
    ∃ p : S → Option S → ℝ,
      (∀ i l, 0 ≤ p i l) ∧ (∀ i, ∑ l, p i l = 1) ∧
      (∑ l, J.energy μ (fun i => √(p i l))) ≤
        4*((η+κ)*Real.log (Fintype.card (Option S))) ∧
      (∑ i, μ i*b i*p i none) ≤ 2*η ∧
      (∀ s i, μ i*p i (some s) ≤ (μ s*b s/η)*J.lazy.endpoint η s i) := by
  let K := J.lazy
  have st := J.lazy_stationary μ stat
  let B := K.reverse μ hp st
  have hu (i : S) := (bound i).trans hκ
  let p := B.labels b hb hu η
  let q i l := B.average (fun j => p j l) i
  have pp := B.labels_nonneg b hb hu hη h1
  have sp := B.labels_sum b hb hu hη h1
  have qp (i : S) (l : Option S) : 0 ≤ q i l := B.average_nonneg (fun j => pp j l) i
  have sq (i : S) : ∑ l, q i l = 1 := by
    dsimp only [q,average]; rw [sum_comm]; simp only [← mul_sum,p,sp,mul_one,B.row]
  have flow (i : S) (l : Option S) : μ i*q i l = K.advance (fun j => μ j*p j l) i :=
    K.reverse_average μ hp st _ i
  have he := collected_energy J μ hp stat p q pp qp flow
  have logpos : 0 ≤ Real.log (Fintype.card (Option S)) :=
    Real.log_nonneg (by simp [Fintype.card_option])
  have gap (i : S) := refresh_gap (p i) (q i) (qp i) (sq i) i hη.le h1.le (hb i) (hu i)
    (B.labels_rec b hb hu hη h1 i)
  have gap' (i : S) : μ i*(negEntropy (p i)-negEntropy (q i)) ≤
      μ i*((η+κ)*Real.log (Fintype.card (Option S))) :=
    mul_le_mul_of_nonneg_left ((gap i).trans (mul_le_mul_of_nonneg_right (by linarith [bound i]) logpos)) (hp i)
  have total := sum_le_sum (s := univ) (fun i _ => gap' i)
  rw [← sum_mul,hs,one_mul] at total
  refine ⟨p,pp,sp,he.trans (by linarith only [total]),?_,K.label_endpoint_bound μ hp st b hb hu hη h1⟩
  let D := ∑ i, μ i*p i none
  let A := ∑ i, μ i*b i*q i none
  have hn : 0 ≤ D := sum_nonneg fun i _ => mul_nonneg (hp i) (pp i none)
  have sumq : ∑ i, μ i*q i none = D := by simp only [flow,K.advance_sum,D]
  have one (i : S) : μ i*p i none = μ i*η + (1-η)*(μ i*q i none) - (1-η)*(μ i*b i*q i none) := by
    have h := B.labels_rec b hb hu hη h1 i none
    change p i none = _ at h
    rw [h]; simp [q,average]; ring
  have mass : D = η + (1-η)*D - (1-η)*A := by
    change (∑ i, μ i*p i none) = _
    simp only [one,sum_sub_distrib,sum_add_distrib,← sum_mul,← mul_sum,hs,one_mul,sumq,A]
  have lost : (1-η)*A ≤ η := by nlinarith only [mass,mul_nonneg hη.le hn]
  have point (i : S) : μ i*b i*p i none ≤ μ i*η + (1-η)*(μ i*b i*q i none) := by
    have h := congrArg (b i * ·) (one i)
    have h0 := mul_le_of_le_one_left (mul_nonneg (hp i) hη.le) (hu i)
    have non := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr h1.le) (hp i)) (hb i)) (hb i)) (qp i none)
    nlinarith only [h,h0,non]
  have last := sum_le_sum (s := univ) (fun i _ => point i)
  rw [sum_add_distrib,← sum_mul,hs,one_mul,← mul_sum] at last
  change _ ≤ η + (1-η)*A at last
  linarith only [last,lost]

end TwoSAT.Walk.Kernel

end

section

namespace TwoSAT.Walk.Kernel

open Finset TwoSAT.Entropy

variable {S : Type} [Fintype S] [DecidableEq S]

private theorem scale_roots (c x y : ℝ) (hc : 0 ≤ c) :
    √(c*x)*√(c*y) = c*(√x*√y) := by
  simp only [Real.sqrt_mul hc]
  nlinarith only [congrArg (· * (√x*√y)) (Real.mul_self_sqrt hc)]

/-- Compare the affinity of the refreshed labels on a symmetric set to the affinity
of the original geometrically stopped walk started there. -/
theorem local_affinity_transfer (K : Kernel S) (μ b : S → ℝ) (hp : ∀ i, 0 ≤ μ i)
    (e : S ≃ S) (sym : ∀ i, μ (e i) = μ i) (symb : ∀ i, b (e i) = b i)
    {κ η : ℝ} (hb : ∀ i, 0 ≤ b i) (bound : ∀ i, b i ≤ κ) (hη : 0 < η)
    (p : S → Option S → ℝ) (hn : ∀ i l, 0 ≤ p i l) (dummy : (∑ i, μ i*b i*p i none) ≤ 2*η)
    (dom : ∀ s i, μ i*p i (some s) ≤ (μ s*b s/η)*K.endpoint η s i) :
    (∑ i, μ i*b i*affinity (p i) (p (e i))) ≤
      2*η + (κ/η)*∑ s, μ s*b s*K.endpointAffinity η e s := by
  let z i := μ i*b i*p i none
  let m i := μ i*b i*(√(p i none)*√(p (e i) none))
  have edummy (i : S) : m i ≤ (z i+z (e i))/2 := by
    have hg : √(p i none)*√(p (e i) none) ≤ (p i none+p (e i) none)/2 := by
      nlinarith only [sq_nonneg (√(p i none)-√(p (e i) none)),Real.sq_sqrt (hn i none),Real.sq_sqrt (hn (e i) none)]
    dsimp only [m,z]; rw [sym,symb]
    linarith only [mul_le_mul_of_nonneg_left hg (mul_nonneg (hp i) (hb i))]
  have hD := sum_le_sum (s := univ) (fun i _ => edummy i)
  simp only [← sum_div,sum_add_distrib,e.sum_comp z] at hD
  let f i s := μ i*b i*(√(p i (some s))*√(p (e i) (some s)))
  have hF (i s : S) : f i s ≤ (κ/η)*(μ s*b s*(√(K.endpoint η s i)*√(K.endpoint η s (e i)))) := by
    let c := μ s*b s/η
    have hc : 0 ≤ c := div_nonneg (mul_nonneg (hp s) (hb s)) hη.le
    have hh := mul_le_mul (Real.sqrt_le_sqrt (dom s i)) (Real.sqrt_le_sqrt (dom s (e i)))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [sym,scale_roots _ _ _ (hp i),scale_roots _ _ _ hc] at hh
    have le := (mul_le_mul_of_nonneg_right (bound i)
      (mul_nonneg (hp i) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))).trans
      (mul_le_mul_of_nonneg_left hh ((hb i).trans (bound i)))
    dsimp [f]
    dsimp [c] at le
    simp only [div_eq_mul_inv] at le ⊢
    linarith only [le]
  have hh := sum_le_sum (s := univ) (fun i _ => sum_le_sum (s := univ) (fun s _ => hF i s))
  conv_rhs at hh => rw [sum_comm]
  simp only [← mul_sum] at hh
  change (∑ i, ∑ s, f i s) ≤ (κ/η)*∑ s, μ s*b s*K.endpointAffinity η e s at hh
  have expand (i : S) : μ i*b i*affinity (p i) (p (e i)) = m i + ∑ s, f i s := by
    simp only [affinity,Fintype.sum_option,mul_add,mul_sum,m,f]
  simp only [expand,sum_add_distrib]
  change (∑ i, z i) ≤ 2*η at dummy
  linarith only [hh,hD,dummy]

end TwoSAT.Walk.Kernel

end

section

namespace TwoSAT.ClauseLaw

open Finset TwoSAT.Walk TwoSAT.Weights TwoSAT.Balance TwoSAT.Entropy

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]

/-- Combine the threshold, rounding, and stationary refreshed-label estimates. -/
theorem two_way_inequality (u v : E → Literal V) (w : E → ℝ) (hw : ∀ i, 0 ≤ w i)
    (sw : ∑ i, w i = 1) (bal : ∀ x, imbalance u v w x = 0)
    {δ η κ scale t : ℝ} (hη : 0 < η) (half : η ≤ 1/2) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hscale : 0 < scale) (ht : 0 < t) (err : √(32*η)/scale ≤ δ/2)
    (far : ∀ a, δ ≤ ∑ i, w i * charge 1 a (u i) (v i)) :
    let a := (forward u v w hw).lazy.endpointAffinity η flipPerm
    let B := ∑ i, seed u v w i * min (a i) (a i.flip)
    δ ≤ 8*(η/κ) + 4*(κ/η)*(2*scale+B) + 2*t +
      (8/t)*((η+κ)*Real.log (Fintype.card (Option (Literal V)))) := by
  let J := forward u v w hw
  let μ := seed u v w
  let a := J.lazy.endpointAffinity η flipPerm
  let q (i : Literal V) := a i.flip-a i
  obtain ⟨θ,_,loss,_,upper⟩ := TwoSAT.Cutoff.balanced_cutoff u v w hw sw bal hη half hscale err far
  let keep (i : Literal V) := decide (|q i| ≤ θ)
  let b (i : Literal V) := if keep i then κ else 0
  have sym := seed_balanced u v w bal
  have ks (i : Literal V) : keep i.flip = keep i := by simp [keep,q,abs_sub_comm]
  have symb (i : Literal V) : b (flipPerm i) = b i := by change b i.flip = _; simp [b,ks]
  have hb (i) : 0 ≤ b i := by dsimp [b]; split_ifs <;> simp [hκ.le]
  have bu (i) : b i ≤ κ := by dsimp [b]; split_ifs <;> simp [hκ.le]
  have hp := seed_nonneg u v hw
  have hs := (seed_total u v w).trans sw
  obtain ⟨p,hn,sp,energy,missing,dom⟩ := J.localized_labels μ hp hs (stationary u v w hw sym) b hb hκ1 bu hη (by linarith)
  have lower (t' : V → Bool) : δ/2 ≤ ∑ i, (if keep (u i) && keep (v i) then w i else 0)*charge 1 t' (u i) (v i) := by
    simpa [keep,TwoSAT.Cutoff.internal,q,a,J] using loss t'
  have round := TwoSAT.ColumnRounding.retained_rounding u v w hw sw keep p hn sp ht lower
  have transfer := J.lazy.local_affinity_transfer μ b hp flipPerm sym symb hb bu hη p hn missing dom
  let c (i : Literal V) := affinity (p i) (p i.flip)
  let total (f : Literal V → ℝ) := ∑ i, μ i*(if keep i then f i else 0)
  have restrict (f : Literal V → ℝ) : (∑ i, μ i*b i*f i) = κ*total f := by
    rw [show κ*total f = ∑ i, κ*(μ i*(if keep i then f i else 0)) from mul_sum ..]
    apply sum_congr rfl; intro i _; dsimp [b]; split_ifs <;> ring
  change (∑ i, μ i*b i*c i) ≤ 2*η+(κ/η)*∑ i, μ i*b i*a i at transfer
  rw [restrict,restrict] at transfer
  have upper' : total a ≤ 2*scale+∑ i, μ i*min (a i) (a i.flip) := by
    simpa [total,keep,q,a,J,μ] using upper
  have rr : total c ≤ 2*(η/κ)+(κ/η)*total a := by
    apply (mul_le_mul_iff_of_pos_left hκ).mp
    apply transfer.trans_eq
    field_simp
  change 2*(δ/2) ≤ 4*total c + 2*t + (2/t)*∑ l, J.energy μ (fun i => √(p i l)) at round
  dsimp only
  change δ ≤ 8*(η/κ)+4*(κ/η)*(2*scale+∑ i, μ i*min (a i) (a i.flip)) + 2*t +
    (8/t)*((η+κ)*Real.log (Fintype.card (Option (Literal V))))
  have comparison := mul_le_mul_of_nonneg_left upper' (div_nonneg hκ.le hη.le)
  have control := mul_le_mul_of_nonneg_left energy (show 0 ≤ 2/t by positivity)
  simp only [div_eq_mul_inv] at round rr comparison control ⊢
  linarith only [round,rr,comparison,control]

end TwoSAT.ClauseLaw

end

section

namespace TwoSAT.ClauseLaw

open Finset TwoSAT.Weights TwoSAT.Walk

/-- The dimension-dependent denominator of the stopping probability is logarithmic. -/
noncomputable def logSize (V : Type) [Fintype V] := 1+Real.log (Fintype.card (Option (Literal V)))

theorem logSize_one (V : Type) [Fintype V] : 1 ≤ logSize V := by
  dsimp [logSize]
  linarith only [Real.log_nonneg (show (1:ℝ) ≤ Fintype.card (Option (Literal V)) by simp [Fintype.card_option])]

/-- The two-way affinity conclusion of Theorem 5.1, with constants depending only on δ. -/
theorem balanced_affinity {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ γ β : ℝ, 0 < γ ∧ γ ≤ 1/2 ∧ 0 < β ∧
    ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
      (u v : E → Literal V) (w : E → ℝ) (hw : ∀ i, 0 ≤ w i) (_sw : ∑ i, w i = 1)
      (_bal : ∀ x, imbalance u v w x = 0) (_far : ∀ a, δ ≤ ∑ i, w i*charge 1 a (u i) (v i)),
      let a := (forward u v w hw).lazy.endpointAffinity (γ/logSize V) flipPerm
      β ≤ ∑ i, seed u v w i * min (a i) (a i.flip) := by
  let r := δ/128
  let scale := r*δ/128
  let t := δ/8
  let c := min (δ^2/1024) (scale^2*δ^2/(128*r))
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hc1 : c ≤ 1/2 := (min_le_left ..).trans (by nlinarith [sq_nonneg (1-δ),mul_nonneg hδ.le (sub_nonneg.mpr hδ1)])
  refine ⟨r*c,r*δ/16,mul_pos hr hc,(mul_le_of_le_one_left hc.le hr1).trans hc1,by positivity,?_⟩
  intro V E _ _ _ u v w hw sw bal far
  let L := logSize V
  let κ := c/L
  let η := r*c/L
  have hL : 1 ≤ L := logSize_one V
  have hL0 : 0 < L := by linarith
  have hκ : 0 < κ := div_pos hc hL0
  have hκc : κ ≤ c := div_le_self hc.le hL
  have hη : 0 < η := div_pos (mul_pos hr hc) hL0
  have ratio : η = r*κ := by dsimp [η,κ]; ring
  have hηκ : η ≤ κ := ratio.trans_le (mul_le_of_le_one_left hκ.le hr1)
  have err : √(32*η)/scale ≤ δ/2 := by
    apply (div_le_iff₀ hscale).mpr
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    have h := (le_div_iff₀ (show 0 < 128*r by positivity)).mp (min_le_right (δ^2/1024) (scale^2*δ^2/(128*r)))
    change c*(128*r) ≤ _ at h
    nlinarith only [h,mul_le_mul_of_nonneg_left hκc hr.le,ratio]
  let B := ∑ i, seed u v w i * min ((forward u v w hw).lazy.endpointAffinity η flipPerm i)
    ((forward u v w hw).lazy.endpointAffinity η flipPerm i.flip)
  have H := two_way_inequality u v w hw sw bal hη (hηκ.trans (hκc.trans hc1)) hκ
    (hκc.trans (hc1.trans (by norm_num))) hscale ht err far
  change δ ≤ 8*(η/κ)+4*(κ/η)*(2*scale+B)+2*t+(8/t)*((η+κ)*_) at H
  have r1 : η/κ = r := (div_eq_iff hκ.ne').mpr ratio
  have r2 : κ/η = 1/r := by rw [ratio]; field_simp
  rw [r1,r2] at H
  have logLe : Real.log (Fintype.card (Option (Literal V))) ≤ L := by dsimp [L,logSize]; linarith
  have prod : (η+κ)*Real.log (Fintype.card (Option (Literal V))) ≤ 2*c := by
    apply (mul_le_mul_of_nonneg_left logLe (add_nonneg hη.le hκ.le)).trans
    have eqn : κ*L = c := div_mul_cancel₀ _ hL0.ne'
    linarith only [mul_le_mul_of_nonneg_right hηκ hL0.le,eqn]
  have last : (8/t)*((η+κ)*Real.log (Fintype.card (Option (Literal V)))) ≤ δ/8 := by
    apply (mul_le_mul_of_nonneg_left prod (by positivity : 0 ≤ 8/t)).trans
    rw [div_mul_eq_mul_div,div_le_iff₀ ht]
    dsimp [t]; nlinarith only [show c ≤ δ^2/1024 from min_le_left ..]
  change r*δ/16 ≤ B
  have hB : δ ≤ 8*r+4*(1/r)*(2*scale+B)+2*t+δ/8 := by linarith only [H,last]
  have F := mul_le_mul_of_nonneg_left hB hr.le
  field_simp [hr.ne'] at F
  dsimp [scale,t,r] at F ⊢
  nlinarith only [F]

end TwoSAT.ClauseLaw

end

section

namespace TwoSAT.ClauseLaw

open Finset TwoSAT.Entropy TwoSAT.Balance TwoSAT.Walk TwoSAT.Weights

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]

noncomputable def twoWayMean (K : Kernel (Literal V)) (μ : Literal V → ℝ) (η : ℝ) :=
  ∑ s, μ s * min (K.endpointAffinity η flipPerm s) (K.endpointAffinity η flipPerm s.flip)

private noncomputable def start (j : Bool) : Literal V ≃ Literal V :=
  if j then flipPerm else Equiv.refl _

private noncomputable def joint (K : Kernel (Literal V)) (μ : Literal V → ℝ) (η : ℝ)
    (j : Bool) (i : Literal V × Literal V) := μ i.1*K.endpoint η (start j i.1) i.2

private theorem mean_eq (K : Kernel (Literal V)) (μ : Literal V → ℝ) (hp : ∀ i, 0 ≤ μ i) (η : ℝ) :
    twoWay flipPerm (joint K μ η false) (joint K μ η true) = twoWayMean K μ η := by
  have r (s : Literal V) (j : Bool) : row flipPerm (joint K μ η j) s =
      μ s*K.endpointAffinity η flipPerm (start j s) := by
    unfold row Kernel.endpointAffinity affinity joint
    rw [mul_sum]; apply sum_congr rfl; intro i _
    simp only [Real.sqrt_mul (hp s)]
    nlinarith only [congrArg (fun z => z*(√(K.endpoint η (start j s) i)*√(K.endpoint η (start j s) (flipPerm i)))) (Real.mul_self_sqrt (hp s))]
  apply sum_congr rfl; intro s _
  rw [r s false,r s true,← mul_min_of_nonneg _ _ (hp s)]
  rfl

theorem compare_clauses (u v : E → Literal V) (π w : E → ℝ) (hb : ∀ i, 0 < π i)
    (hw : ∀ i, 0 ≤ w i) (sπ : ∑ i, π i = 1) (sw : ∑ i, w i = 1)
    (bal : ∀ x, imbalance u v w x = 0) {η β d : ℝ} (hη : 0 < η) (hu : η < 1)
    (hβ : 0 < β) (hd : 0 ≤ d)
    (budget : divergence (seed u v w) (seed u v π) + ((1-η)/(2*η))*clausePenalty u v π w ≤ d)
    (high : β ≤ twoWayMean (forward u v w hw).lazy (seed u v w) η) :
    β/2*Real.exp (-(64*(d+1)/β^2)) ≤ twoWayMean (forward u v π (fun i => (hb i).le)).lazy (seed u v π) η := by
  let Q := (forward u v w hw).lazy
  let P := (forward u v π (fun i => (hb i).le)).lazy
  let μ := seed u v w
  let ρ := seed u v π
  have hμ := seed_nonneg u v hw
  have hρ := seed_nonneg u v (fun i => (hb i).le)
  have non (K : Kernel (Literal V)) (m : Literal V → ℝ) (hm : ∀ i, 0 ≤ m i) (j i) :
      0 ≤ joint K m η j i := mul_nonneg (hm _) (K.endpoint_nonneg hη hu ..)
  have mass1 (K : Kernel (Literal V)) (m : Literal V → ℝ) (hm : ∑ i, m i = 1) (j : Bool) :
      ∑ i, joint K m η j i = 1 := by simp only [joint,Fintype.sum_prod_type,← mul_sum,K.endpoint_row hη hu,mul_one,hm]
  have kl (j : Bool) : divergence (joint Q μ η j) (joint P ρ η j) ≤ d := by
    have sym (s : Literal V) : μ (start j s) = μ s := by
      cases j
      · rfl
      · exact seed_balanced u v w bal s
    exact (joint_clause_divergence u v π w hb hw bal (start j) (Equiv.refl _) sym hη hu).trans budget
  have supp (j : Bool) (i : Literal V × Literal V) (h : 0 < joint Q μ η j i) : 0 < joint P ρ η j i :=
    mul_pos (seed_support u v π w hb hw _ (pos_of_mul_pos_left h (Q.endpoint_nonneg hη hu ..)))
      (Kernel.geometric_support (lazy_support u v π w hb hw) hη hu _ _ (pos_of_mul_pos_right h (hμ _)))
  rw [← mean_eq P ρ hρ]
  apply compare_twoWay flipPerm _ _ hβ hd (non Q μ hμ) (non P ρ hρ)
    (mass1 Q μ ((seed_total u v w).trans sw)) (mass1 P ρ ((seed_total u v π).trans sπ)) supp kl
  rwa [mean_eq Q μ hμ]

end TwoSAT.ClauseLaw

end

section

namespace TwoSAT.Entropy

/-- Convert the KL comparison into polynomially small two-way affinity. -/
theorem comparison_power {D b γ α ν x : ℝ} (hb : 0 < b) (hγ : 0 < γ) (hx : 1 ≤ x)
    (small : 32*α ≤ ν*γ*b^2) :
    let η := γ/(1+Real.log x)
    let C := b/2 * Real.exp (-(64*(D+1)/b^2)-ν/2)
    C*x^(-ν/2) ≤ b/2*Real.exp (-(64*(D+α/(4*η)+1)/b^2)) := by
  intro η C
  have hx0 : 0 < x := by linarith
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : 16*α/(γ*b^2) ≤ ν/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [small]
  have h2 : 64*(α/(4*η))/b^2 = (16*α/(γ*b^2))*(1+Real.log x) := by
    dsimp [η]; field_simp [show 1+Real.log x ≠ 0 by linarith]; ring
  have h3 := mul_le_mul_of_nonneg_right h1 (show 0 ≤ 1+Real.log x by linarith)
  rw [← h2] at h3
  dsimp only [C]
  rw [Real.rpow_def_of_pos hx0,mul_assoc,← Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by positivity)
  simp only [div_eq_mul_inv] at h3 ⊢
  linarith only [h3]

end TwoSAT.Entropy

end

section

namespace TwoSAT.ClauseLaw

open Finset TwoSAT.Weights TwoSAT.Balance TwoSAT.Entropy

/-- The locally samplable clause distribution has polynomially large two-way affinity.
All constants precede the choice of the input or its number of variables. -/
theorem accessible_affinity {δ ν : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 < ν) :
    ∃ γ β c : ℝ, 0 < γ ∧ γ ≤ 1/2 ∧ 0 < β ∧ 0 < c ∧
    ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
      (u v : E → Literal V) (π : E → ℝ) (hπ : ∀ i, 0 < π i), (∑ i, π i = 1) →
      (∀ t, δ ≤ ∑ i, π i*charge 1 t (u i) (v i)) → (∑ x, |imbalance u v π x|) ≤ β →
      c*(Fintype.card (Option (Literal V)) : ℝ)^(-ν/2) ≤
        twoWayMean (forward u v π (fun i => (hπ i).le)).lazy (seed u v π) (γ/logSize V) := by
  let h := δ^2/1600
  have hh : 0 < h := by dsimp [h]; positivity
  have h2 : 2*h ≤ 1 := by dsimp [h]; nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ1)]
  have hh1 : h ≤ 1 := by linarith
  obtain ⟨γ,b,hγ,hγ1,hb,balanced⟩ := balanced_affinity hh hh1
  let α := min 1 (ν*γ*b^2/32)
  have ha : 0 < α := lt_min zero_lt_one (by positivity)
  let D := Real.log (1/(2*h))
  have hD : 0 ≤ D := Real.log_nonneg ((le_div_iff₀ (by positivity)).mpr (by linarith))
  let C := b/2*Real.exp (-(64*(D+1)/b^2)-ν/2)
  have small : 32*α ≤ ν*γ*b^2 := by linarith only [show α ≤ ν*γ*b^2/32 from min_le_right ..]
  refine ⟨γ,α*δ^2/400,C,hγ,hγ1,by positivity,by dsimp [C]; positivity,?_⟩
  intro V E _ _ _ u v π hπ sπ far near
  obtain ⟨w,hw,sw,bal,_,wf,pen,kl⟩ := balanced_distribution u v π hπ sπ hδ hδ1 ha (min_le_left ..) far near
  have wfar (t : V → Bool) : h ≤ ∑ i, w i*charge 1 t (u i) (v i) := by
    apply (wf t).trans_eq (sum_congr rfl (fun i _ => ?_))
    unfold charge; split_ifs <;> simp
  let x := (Fintype.card (Option (Literal V)) : ℝ)
  have hx : 1 ≤ x := by simp [x,Fintype.card_option]
  let η := γ/logSize V
  have hL := logSize_one V
  have pos : 0 < η := div_pos hγ (by linarith)
  have hu : η < 1 := (div_le_self hγ.le hL).trans_lt (by linarith)
  have budget : divergence (seed u v w) (seed u v π) + (1-η)/(2*η)*clausePenalty u v π w ≤
      D+α/(4*η) := by
    apply add_le_add kl
    apply (mul_le_mul_of_nonneg_left pen (div_nonneg (sub_nonneg.mpr hu.le) (by positivity))).trans
    apply (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (show 1-η ≤ 1 by linarith) (by positivity : 0 ≤ 2*η)) (by positivity : 0 ≤ α/2)).trans_eq
    ring
  have h := compare_clauses u v π w hπ hw sπ sw bal pos hu hb (add_nonneg hD (by positivity)) budget
    (balanced u v w hw sw bal wfar)
  exact (comparison_power (D := D) hb hγ hx small).trans h

end TwoSAT.ClauseLaw

end

section

namespace TwoSAT.LocalWeights

open Finset TwoSAT.Weights TwoSAT.ClauseLaw

variable {n d : ℕ}

noncomputable def clauseWeight (d T : ℕ) (o : Oracle n d) (c : Clause (Fin n)) :=
  max 0 (localWeight d T (forbidden c).1 (forbidden c).2 o)

theorem clauseWeight_nonneg (T : ℕ) (o : Oracle n d) (c : Clause (Fin n)) : 0 ≤ clauseWeight d T o c :=
  le_max_left ..

theorem seed_per_literal (F : Input n d) (hF : Reduction.Exact F) (w : Edges F → ℝ)
    (hw : ∀ e, w e ≤ 1) (s : Literal (Fin n)) : seed (left F) (right F) w s ≤ d/2 := by
  let u := left F
  let v := right F
  have sum : seed u v w s = ∑ e, ((if u e=s then w e else 0)+(if v e=s then w e else 0))/2 := by
    simp only [seed,mass,Fintype.sum_prod_type,Fintype.sum_bool,side,oriented,if_true,
      Bool.false_eq_true,if_false]
    apply sum_congr rfl; intro i _; split_ifs <;> ring
  rw [sum,← sum_div]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply le_trans _ (show ((occurrences u v s.var : ℕ) : ℝ) ≤ d by exact_mod_cast occurrence_bound F hF s.var)
  unfold occurrences
  push_cast
  apply sum_le_sum; intro i _
  have hi := hw i
  by_cases a : u i=s <;> by_cases b : v i=s <;> simp [a,b] <;> (try split_ifs) <;> simp_all <;> linarith only [hi]

/-- Local evaluation yields the normalized law and a constant-factor comparison with
a uniform literal seed on far inputs. -/
theorem local_law (d : ℕ) (hd : 0 < d) {ε ν : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hν : 0 < ν) :
    ∃ T q : ℕ, ∃ γ c a : ℝ, 0 < γ ∧ γ ≤ 1/2 ∧ 0 < c ∧ 0 < a ∧
    (∀ n (u v : Literal (Fin n)), Query.Bounded q (localWeight d T u v)) ∧
    ∀ n, 0 < n → ∀ F : Input n d, Reduction.Exact F → ε*d*n ≤ distance F.formula →
      let w := fun e : Edges F => clauseWeight d T F.oracle e.val
      let W := ∑ e, w e
      let π := fun e => w e/W
      ∃ pos : ∀ i, 0 < π i, (∑ i, π i = 1) ∧ 0 < W ∧
      (∀ s, a*seed (left F) (right F) π s ≤ 1/(2*n)) ∧
      c*(Fintype.card (Option (Literal (Fin n))) : ℝ)^(-ν/2) ≤
        twoWayMean (forward (left F) (right F) π (fun i => (pos i).le)).lazy
          (seed (left F) (right F) π) (γ/logSize (Fin n)) := by
  let k := ε/4*Real.exp (-4/ε)
  have hk : 0 < k := by dsimp [k]; positivity
  have hk1 : k/2 ≤ 1 := by
    have he := Real.exp_le_one_iff.mpr (show -4/ε ≤ 0 by exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hε.le)
    dsimp [k]; nlinarith only [mul_le_mul_of_nonneg_left he hε.le,hε1]
  obtain ⟨γ,β,c,hγ,hγ1,hβ,hc,aff⟩ := accessible_affinity (show 0 < k/2 by positivity) hk1 hν
  obtain ⟨T,q,cost,weights⟩ := local_weight_theorem d hd ε β hε hβ
  refine ⟨T,q,γ,c,k*ε,hγ,hγ1,hc,mul_pos hk hε,cost,?_⟩
  intro n hn F hF far
  let w (e : Edges F) := localWeight d T (left F e) (right F e) F.oracle
  let W := ∑ e, w e
  let π (e : Edges F) := w e/W
  obtain ⟨hw,lb,near,loss⟩ := weights n hn F hF far
  have eqw (e : Edges F) : clauseWeight d T F.oracle e.val = w e := max_eq_right (hw e).1.le
  simp only [eqw]
  have edge : ε*d*n ≤ (Fintype.card (Edges F) : ℝ) := by
    let t (_ : Fin n) := false
    have hl : distance F.formula ≤ TwoSAT.loss t F.formula := Nat.sInf_le ⟨t,rfl⟩
    apply (far.trans (show (distance F.formula : ℝ) ≤ (TwoSAT.loss t F.formula : ℝ) by exact_mod_cast hl)).trans
    rw [edge_loss F hF t]
    apply le_trans (sum_le_sum (g := fun _ : Edges F => (1:ℝ)) (fun i _ => ?_)) (by simp)
    unfold charge; split_ifs <;> norm_num
  change k*(Fintype.card (Edges F) : ℝ) ≤ W at lb
  have hl : k*ε*(d:ℝ)*n ≤ W := by linarith only [lb,mul_le_mul_of_nonneg_left edge hk.le]
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hW : 0 < W := lt_of_lt_of_le (by positivity) hl
  have pos (i : Edges F) : 0 < π i := div_pos (hw i).1 hW
  have sp : ∑ i, π i = 1 := by simp only [π,← sum_div,show ∑ i, w i = W from rfl,div_self hW.ne']
  refine ⟨pos,sp,hW,?_,aff (left F) (right F) π pos sp ?_ ?_⟩
  · intro s
    have normalized : seed (left F) (right F) π s = seed (left F) (right F) w s / W := by
      simp only [seed,mass,oriented,π,sum_div]; apply sum_congr rfl; intro i _
      split_ifs <;> ring
    rw [normalized,le_div_iff₀ (by positivity)]
    have h := seed_per_literal F hF w (fun i => (hw i).2) s
    apply (le_of_mul_le_mul_right _ hW)
    field_simp [hW.ne']
    nlinarith only [hl,mul_le_mul_of_nonneg_left h (show 0 ≤ 2*(k*ε*(n:ℝ)) by positivity)]
  · intro t
    apply (loss t).trans_eq
    rw [sum_div]
    apply sum_congr rfl; intro i _; change charge (w i) t (left F i) (right F i)/W = (w i/W)*charge 1 t (left F i) (right F i)
    unfold charge; split_ifs <;> ring
  · have eqn (x : Fin n) : imbalance (left F) (right F) π x =
        imbalance (left F) (right F) w x / W := by
      simp [imbalance,π,sum_div,mul_div_assoc]
    simp only [eqn,abs_div,abs_of_pos hW,← sum_div]
    exact near

end TwoSAT.LocalWeights

end

section

namespace TwoSAT.Collision

open Finset
open scoped BigOperators

variable {Ω I S : Type*} [Fintype Ω] [Fintype I] [Fintype S]

noncomputable def mean (p f : Ω → ℝ) := ∑ z, p z * f z

noncomputable def batch (p : Ω → ℝ) (x : I → Ω) := ∏ j, p (x j)

theorem mean_sum (p : Ω → ℝ) (f : I → Ω → ℝ) :
    mean p (fun z => ∑ j, f j z) = ∑ j, mean p (f j) := by
  simp only [mean, mul_sum]; rw [sum_comm]

theorem mean_scale (p f : Ω → ℝ) (a : ℝ) :
    mean p (fun z => a * f z) = a * mean p f := by
  simp only [mean, mul_sum]; apply sum_congr rfl; intros; ring

theorem product_mean [DecidableEq I] (p : Ω → ℝ) (g : I → Ω → ℝ) :
    mean (batch p) (fun x : I → Ω => ∏ j, g j (x j)) = ∏ j, mean p (g j) := by
  simp only [mean, batch, ← prod_mul_distrib, Fintype.prod_sum]

theorem batch_mass [DecidableEq I] (p : Ω → ℝ) (hp : ∑ z, p z = 1) :
    ∑ x : I → Ω, batch p x = 1 := by
  simpa [mean, hp] using product_mean p (fun (_ : I) (_ : Ω) => (1 : ℝ))

theorem coordinate_mean [DecidableEq I] (p f : Ω → ℝ) (hp : ∑ z, p z = 1) (i : I) :
    mean (batch p) (fun x : I → Ω => f (x i)) = mean p f := by
  let g (j : I) (z : Ω) := if j = i then f z else 1
  have h (j : I) : mean p (g j) = if j = i then mean p f else 1 := by
    by_cases hj : j = i <;> simp [g, hj, mean, hp]
  simpa [g, h] using product_mean p g

theorem distinct_coordinates [DecidableEq I] (p f g : Ω → ℝ) (hp : ∑ z, p z = 1)
    {i j : I} (hne : i ≠ j) :
    mean (batch p) (fun x : I → Ω => f (x i) * g (x j)) = mean p f * mean p g := by
  let v (k : I) (z : Ω) := (if k = i then f z else 1) * (if k = j then g z else 1)
  have h (k : I) : mean p (v k) =
      (if k = i then mean p f else 1) * (if k = j then mean p g else 1) := by
    by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all [v, mean]
  simpa only [h, v, prod_mul_distrib, prod_ite_eq', mem_univ, if_true] using product_mean p v

/-- Factorization across the two independent batches. -/
theorem independent_mean (p f : Ω → ℝ) (q g : S → ℝ) :
    mean (fun xy : Ω × S => p xy.1 * q xy.2) (fun xy => f xy.1 * g xy.2) =
      mean p f * mean q g := by
  simp only [mean, Fintype.sum_prod_type, sum_mul]
  apply sum_congr rfl
  intro z _
  rw [mul_sum]
  apply sum_congr rfl
  intros; ring

noncomputable def count [DecidableEq Ω] (x : I → Ω) (z : Ω) : ℝ :=
  ∑ i, if x i = z then 1 else 0

theorem mean_count [DecidableEq Ω] [DecidableEq I] (p : Ω → ℝ) (hp : ∑ z, p z = 1) (z : Ω) :
    mean (batch p) (fun x : I → Ω => count x z) = Fintype.card I * p z := by
  unfold count
  rw [mean_sum]
  have h (i : I) : mean (batch p) (fun x : I → Ω => if x i = z then 1 else 0) = p z := by
    convert coordinate_mean p (fun w => if w = z then 1 else 0) hp i using 1
    simp [mean, mul_ite]
  simp [h]

private theorem count_pair {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq I] [DecidableEq Ω]
    (p : Ω → ℝ) (hp : ∑ z, p z = 1) (i j : I) (z w : Ω) :
    mean (batch p) (fun x : I → Ω => (if x i = z then 1 else 0) * (if x j = w then 1 else 0)) =
    p z * p w + (if j = i then (if z = w then p z else 0) - p z * p w else 0) := by
  by_cases hij : i = j
  · subst j
    have hh := coordinate_mean p (fun v => (if v = z then (1:ℝ) else 0) *
      (if v = w then 1 else 0)) hp i
    rw [hh]
    by_cases h : z = w
    · subst w; simp [mean, mul_ite]
    · simp [mean, mul_ite, h, Ne.symm h]
  · rw [distinct_coordinates p (fun v => if v = z then 1 else 0)
        (fun v => if v = w then 1 else 0) hp hij]
    simp [mean, mul_ite, Ne.symm hij]

theorem mean_count_product [DecidableEq Ω] [DecidableEq I] (p : Ω → ℝ)
    (hp : ∑ z, p z = 1) (z w : Ω) :
    mean (batch p) (fun x : I → Ω => count x z * count x w) =
      (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) * p z * p w +
      (if z = w then (Fintype.card I : ℝ) * p z else 0) := by
  simp only [count, sum_mul, mul_sum, mean_sum, count_pair p hp, sum_add_distrib]
  by_cases h : z = w <;> simp [h] <;> ring

end TwoSAT.Collision

end

section

namespace TwoSAT.Sampler

open Finset

variable {α β : Type} {n d : ℕ}

noncomputable def mass (p : PMF α) (x : α) := (p x).toReal

theorem mass_nonneg (p : PMF α) (x : α) : 0 ≤ mass p x := ENNReal.toReal_nonneg

theorem mass_sum [Fintype α] (p : PMF α) : ∑ x, mass p x = 1 := by
  have h := p.tsum_coe
  rw [tsum_fintype] at h
  simp only [mass,← ENNReal.toReal_sum (fun i _ => p.apply_ne_top i),h,ENNReal.toReal_one]

noncomputable def ofMass [Fintype α] (p : α → ℝ) (hp : ∀ x, 0 ≤ p x) (sp : ∑ x, p x = 1) : PMF α :=
  PMF.ofFintype (fun x => ENNReal.ofReal (p x)) (by rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hp x),sp]; simp)

@[simp] theorem mass_ofMass [Fintype α] (p : α → ℝ) (hp sp) (x : α) :
    mass (ofMass p hp sp) x = p x := ENNReal.toReal_ofReal (hp x)

theorem mass_bind [Fintype α] (p : PMF α) (q : α → PMF β) (y : β) :
    mass (p.bind q) y = ∑ x, mass p x * mass (q x) y := by
  rw [mass,PMF.bind_apply,tsum_fintype,ENNReal.toReal_sum (fun i _ =>
    ENNReal.mul_ne_top (p.apply_ne_top i) ((q i).apply_ne_top y))]
  simp only [mass,ENNReal.toReal_mul]

theorem mass_map [Fintype α] [DecidableEq β] (p : PMF α) (f : α → β) (y : β) :
    mass (p.map f) y = ∑ x, if y=f x then mass p x else 0 := by
  classical
  rw [mass,PMF.map_apply,tsum_fintype,ENNReal.toReal_sum (fun i _ => by split_ifs <;> simp [p.apply_ne_top])]
  apply sum_congr rfl; intro i _; split_ifs <;> rfl

@[simp] theorem mass_pure [DecidableEq α] (x y : α) : mass (PMF.pure x) y = if y=x then 1 else 0 := by
  by_cases h : y=x <;> simp [mass,PMF.pure_apply,h]

/-- A randomized sampler of arbitrary output type can serve any subsequent randomized decision. -/
def Cost (k : ℕ) (f : Oracle n d → PMF α) : Prop :=
  ∀ (j : ℕ) (g : α → Oracle n d → PMF Bool), (∀ a, Query.Realizes j (g a)) →
    Query.Realizes (j+k) (fun o => (f o).bind (fun a => g a o))

theorem draw (p : PMF α) : Cost (n := n) (d := d) 0 (fun _ => p) := by
  intro j g hg; exact Query.draw p hg

theorem observe {k} {f : Oracle n d → PMF α} (hf : Query.Bounded k f) : Cost k f := by
  intro j g hg
  exact Query.observe hf (fun p => Query.draw p hg)

theorem bind {j k : ℕ} {f : Oracle n d → PMF α} {g : α → Oracle n d → PMF β}
    (hf : Cost j f) (hg : ∀ a, Cost k (g a)) :
    Cost (j+k) (fun o => (f o).bind (fun a => g a o)) := by
  intro m next h
  have hh := hf (m+k) _ (fun a => hg a m next h)
  rw [show m+(j+k) = m+k+j by omega]
  simpa only [PMF.bind_bind] using hh

theorem map {j : ℕ} {f : Oracle n d → PMF α} (hf : Cost j f) (g : α → β) :
    Cost j (fun o => (f o).map g) := by
  intro m next h
  simpa only [PMF.bind_map,Function.comp_def] using hf m (fun a => next (g a)) (fun a => h (g a))

theorem finish {k : ℕ} {f : Oracle n d → PMF Bool} (hf : Cost k f) : Query.Realizes k f := by
  simpa only [Nat.zero_add,PMF.bind_pure] using hf 0 (fun b _ => PMF.pure b) (fun b => Query.stop b 0)

noncomputable def copies (p : PMF α) : (m : ℕ) → PMF (Fin m → α)
  | 0 => PMF.pure Fin.elim0
  | m+1 => p.bind fun a => (copies p m).map (Fin.cons a)

theorem copies_cost {j : ℕ} {f : Oracle n d → PMF α} (hf : Cost j f) (m : ℕ) :
    Cost (m*j) (fun o => copies (f o) m) := by
  induction m with
  | zero => simpa only [Nat.zero_mul,copies] using (draw (n := n) (d := d) (PMF.pure (Fin.elim0 : Fin 0 → α)))
  | succ m ih =>
    rw [Nat.succ_mul,Nat.add_comm (m*j) j]
    let extend (a : α) (ys : Fin m → α) : Fin (m+1) → α := Fin.cons a ys
    have hg (a : α) := map ih (extend a)
    exact bind (j := j) (k := m*j) (g := fun a o => (copies (f o) m).map (extend a)) hf hg

theorem copies_mass [Fintype α] (p : PMF α) (m : ℕ) (x : Fin m → α) :
    mass (copies p m) x = ∏ i, mass p (x i) := by
  classical
  induction m with
  | zero => simp [copies,Subsingleton.elim x Fin.elim0]
  | succ m ih =>
    rw [copies,mass_bind,Fin.prod_univ_succ]
    have eqn (a : α) (y : Fin m → α) : x=Fin.cons a y ↔ x 0=a ∧ Fin.tail x=y := by
      constructor
      · rintro rfl; simp
      · rintro ⟨rfl,rfl⟩; exact (Fin.cons_self_tail x).symm
    simp only [mass_map,eqn,ite_and]
    simp [mul_ite,ih,Fin.tail]

end TwoSAT.Sampler

end

section

namespace TwoSAT

variable {V : Type} {F : List (Clause V)}

/-- Implications witnessed by individual clauses. Discarded tautologies only add loops. -/
inductive Arc (F : List (Clause V)) : Literal V → Literal V → Prop where
  | unit {a} : Clause.unit a ∈ F → Arc F a.flip a
  | left {a b} : Clause.pair a b ∈ F → Arc F a.flip b
  | right {a b} : Clause.pair a b ∈ F → Arc F b.flip a

theorem Arc.reverseFlip {a b} (h : Arc F a b) : Arc F b.flip a.flip := by
  cases h with
  | unit h => simpa using Arc.unit h
  | left h => simpa using Arc.right h
  | right h => simpa using Arc.left h

abbrev Path (F : List (Clause V)) := Relation.ReflTransGen (Arc F)

theorem reverseFlipPath {a b} (p : Path F a b) : Path F b.flip a.flip := by
  induction p with
  | refl => exact .refl
  | tail _ edge ih => exact Relation.ReflTransGen.head edge.reverseFlip ih

theorem collisionPath {s z : Literal V} (p : Path F s z) (q : Path F s z.flip) :
    Path F s s.flip := p.trans (by simpa using reverseFlipPath q)

theorem Arc.preserves {t : V → Bool} (hs : ∀ c ∈ F, c.eval t = true)
    {a b} (e : Arc F a b) (ha : a.eval t = true) : b.eval t = true := by
  cases e with
  | unit h => exact hs _ h
  | left h =>
    have hh := hs _ h
    simp [Literal.eval_flip] at ha
    simpa [Clause.eval, ha] using hh
  | right h =>
    have hh := hs _ h
    simp [Literal.eval_flip] at ha
    simpa [Clause.eval, ha] using hh

theorem path_preserves {t : V → Bool} (hs : ∀ c ∈ F, c.eval t = true)
    {a b} (p : Path F a b) (ha : a.eval t = true) : b.eval t = true := by
  induction p with
  | refl => exact ha
  | tail _ edge ih => exact edge.preserves hs ih

theorem contradictoryPaths {s : Literal V} (p : Path F s s.flip)
    (q : Path F s.flip s) : ¬ Satisfiable F := by
  rintro ⟨t, ht⟩
  have hs := (loss_eq_zero_iff t F).mp ht
  cases h : s.eval t with
  | false =>
    have hf := path_preserves hs q (by simp [h])
    simp [h] at hf
  | true =>
    have hf := path_preserves hs p h
    simp [h] at hf

/-- The rejection certificate produced by the four endpoint batches in §6.2. -/
theorem fourWalks {s z w : Literal V} (p : Path F s z) (q : Path F s z.flip)
    (r : Path F s.flip w) (u : Path F s.flip w.flip) : ¬ Satisfiable F :=
  contradictoryPaths (collisionPath p q) (by simpa using collisionPath r u)

/-- Any tester whose positive-mass rejecting trees produce the four walks
accepts satisfiable inputs with probability one. -/
theorem rejection_eq_zero_of_fourWalks {n d q} (alg : PMF (Tree n d q)) (input : Input n d)
    (cert : ∀ tree ∈ alg.support, tree.run input.oracle = true →
      ∃ s z w, Path input.formula s z ∧ Path input.formula s z.flip ∧
        Path input.formula s.flip w ∧ Path input.formula s.flip w.flip)
    (hs : Satisfiable input.formula) : rejection alg input = 0 := by
  unfold rejection
  apply (PMF.apply_eq_zero_iff _ _).mpr
  intro hm
  obtain ⟨tree, ht, hrun⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
  obtain ⟨s, z, w, p, q', r, t⟩ := cert tree ht hrun
  exact fourWalks p q' r t hs

end TwoSAT

end

section

namespace TwoSAT.OracleWalk

open Finset TwoSAT.Walk TwoSAT.ClauseLaw TwoSAT.LocalWeights

variable {n d : ℕ}
abbrev L (n : ℕ) := Literal (Fin n)

/-- Mass of the two directed implications of one forbidden pair. -/
noncomputable def contribution (u v s t : L n) (w : ℝ) :=
  (if u=s ∧ v.flip=t then w/2 else 0) + (if v=s ∧ u.flip=t then w/2 else 0)

private theorem contribution_nonneg (u v s t : L n) (w : ℝ) (hw : 0 ≤ w) : 0 ≤ contribution u v s t w := by
  unfold contribution; split_ifs <;> positivity

noncomputable def slot (s : L n) (T : ℕ) (o : Oracle n d) (i : Fin d) (t : L n) :=
  ((o s.var i).map (fun c => contribution (forbidden c).1 (forbidden c).2 s t (clauseWeight d T o c))).getD 0

noncomputable def raw (T : ℕ) (o : Oracle n d) (s t : L n) := ∑ i, slot s T o i t

theorem raw_cost (T q : ℕ) (hf : ∀ (u v : L n), Query.Bounded q (localWeight d T u v)) (s : L n) :
    Query.Bounded (d*(1+q)) (fun o : Oracle n d => raw T o s) := by
  have obs (i : Fin d) : Query.Bounded (1+q) (fun o : Oracle n d => slot s T o i) := by
    let follow (c : Answer n) (o : Oracle n d) (t : L n) :=
      (c.map (fun e => contribution (forbidden e).1 (forbidden e).2 s t (clauseWeight d T o e))).getD 0
    apply Query.bind (g := follow) (Query.read s.var i)
    rintro (_|c)
    · exact Query.map (hf s s) (fun (_ : ℝ) (_ : L n) => (0 : ℝ))
    · exact Query.map (hf (forbidden c).1 (forbidden c).2) (fun z t => contribution (forbidden c).1 (forbidden c).2 s t (max 0 z))
  exact Query.map (Query.gather d (fun i o => slot s T o i) obs) (fun (slots : Fin d → L n → ℝ) (t : L n) => ∑ i, slots i t)

theorem raw_eq (T : ℕ) (F : Input n d) (hF : Reduction.Exact F) (s t : L n) :
    raw T F.oracle s t = flow (left F) (right F) (fun e => clauseWeight d T F.oracle e.val) s t := by
  rw [raw,show (∑ i, slot s T F.oracle i t) = _ from sum_slots F s.var
    (fun c => contribution (forbidden c).1 (forbidden c).2 s t (clauseWeight d T F.oracle c))]
  simp only [flow,Fintype.sum_prod_type]
  apply sum_congr rfl; intro e _
  obtain ⟨a,b,he,_⟩ := hF e.val (List.mem_toFinset.mp e.property)
  simp only [Fintype.sum_bool,side,target,partner,Bool.not_true,Bool.not_false,if_true,
    Bool.false_eq_true,if_false,oriented,left,right,he,forbidden,Literal.flip_flip,contribution,Clause.incident]
  by_cases h : s.var = a.var ∨ s.var = b.var
  · simp [h]
  · have ha : a.flip ≠ s := fun eq => h (Or.inl (show s.var = a.flip.var from congrArg (fun l : L n => l.var) eq.symm))
    have hb : b.flip ≠ s := fun eq => h (Or.inr (show s.var = b.flip.var from congrArg (fun l : L n => l.var) eq.symm))
    simp [h,ha,hb]

/-- Ignore negative weights on arbitrary observations, hold at isolated literals, and make the walk lazy. -/
noncomputable def rowLaw (s : L n) (r : L n → ℝ) : PMF (L n) := by
  let w t := max 0 (r t)
  let W := ∑ t, w t
  let row t := if W=0 then (if s=t then (1:ℝ) else 0) else w t/W
  have hw (t : L n) : 0 ≤ w t := le_max_left ..
  have hW : 0 ≤ W := sum_nonneg fun i _ => hw i
  have hn (t : L n) : 0 ≤ row t := by
    dsimp only [row]; split_ifs <;> first | exact div_nonneg (hw t) hW | norm_num
  have hs : ∑ t, row t = 1 := by
    by_cases h : W=0 <;> simp [row,h,← sum_div,show ∑ t, w t = W from rfl]
  exact Sampler.ofMass (fun t => (if s=t then 1/2 else 0)+1/2*row t)
    (fun t => add_nonneg (by split_ifs <;> norm_num) (mul_nonneg (by norm_num) (hn t))) (by
      simp [sum_add_distrib,← mul_sum,hs]; norm_num)

noncomputable def step (T : ℕ) (s : L n) (o : Oracle n d) := rowLaw s (raw T o s)

theorem step_cost (T q : ℕ) (hf : ∀ (u v : L n), Query.Bounded q (localWeight d T u v)) (s : L n) :
    Sampler.Cost (d := d) (d*(1+q)) (step T s) :=
  Sampler.observe (Query.map (raw_cost T q hf s) (rowLaw s))

theorem step_exact (T : ℕ) (F : Input n d) (hF : Reduction.Exact F) (s t : L n) :
    let w := fun e : Edges F => clauseWeight d T F.oracle e.val
    Sampler.mass (step T s F.oracle) t =
      (forward (left F) (right F) w (fun i => clauseWeight_nonneg T F.oracle i.val)).lazy.prob s t := by
  let w := fun e : Edges F => clauseWeight d T F.oracle e.val
  have eqn (j : L n) : max 0 (raw T F.oracle s j) = flow (left F) (right F) w s j := by
    rw [raw_eq T F hF]; exact max_eq_right (flow_nonneg (left F) (right F) (w := w) (fun i => clauseWeight_nonneg T F.oracle i.val) s j)
  simp only [step,rowLaw,Sampler.mass_ofMass,eqn,flow_row,Kernel.lazy,forward,transition]
  rfl

end TwoSAT.OracleWalk

end

section

namespace TwoSAT.OracleWalk

open Finset TwoSAT.Walk TwoSAT.ClauseLaw TwoSAT.LocalWeights

variable {n d : ℕ}

private theorem forward_scale {V E : Type} [DecidableEq V] [Fintype V] [Fintype E]
    (u v : E → Literal V) (w : E → ℝ) {W : ℝ} (hW : 0 < W) (s t : Literal V) :
    transition u v (fun e => w e/W) s t = transition u v w s t := by
  have seedDiv : seed u v (fun e => w e/W) s = seed u v w s/W := by
    simp only [seed,mass,oriented,sum_div]; apply sum_congr rfl; intro i _; split_ifs <;> ring
  have flowDiv : flow u v (fun e => w e/W) s t = flow u v w s t/W := by
    simp only [flow,oriented,sum_div]; apply sum_congr rfl; intro i _; split_ifs <;> ring
  simp only [transition,seedDiv,flowDiv,div_eq_zero_iff,hW.ne',or_false]
  split_ifs <;> field_simp

theorem normalized_step (T : ℕ) (F : Input n d) (hF : Reduction.Exact F)
    (W : ℝ) (hW : 0 < W) (s t : L n) :
    let π := fun e : Edges F => clauseWeight d T F.oracle e.val/W
    Sampler.mass (step T s F.oracle) t =
      (forward (left F) (right F) π (fun i => div_nonneg (clauseWeight_nonneg T F.oracle i.val) hW.le)).lazy.prob s t := by
  rw [step_exact T F hF]
  simp only [Kernel.lazy,forward,forward_scale _ _ _ hW]

theorem positive_step_path (T : ℕ) (F : Input n d) (hF : Reduction.Exact F)
    (s t : L n) (h : 0 < Sampler.mass (step T s F.oracle) t) : Path F.formula s t := by
  by_cases heq : s=t
  · subst t; exact .refl
  let w (e : Edges F) := clauseWeight d T F.oracle e.val
  have hw (e : Edges F) := clauseWeight_nonneg T F.oracle e.val
  rw [step_exact T F hF] at h
  change 0 < (if s=t then (1/2:ℝ) else 0) + 1/2*transition (left F) (right F) w s t at h
  simp only [heq,if_false,zero_add,transition] at h
  split_ifs at h with hs
  · norm_num at h
  have flowpos : 0 < flow (left F) (right F) w s t := by
    have pos : 0 < flow (left F) (right F) w s t / seed (left F) (right F) w s :=
      pos_of_mul_pos_right h (by norm_num)
    exact (div_pos_iff.mp pos).elim And.left (fun bad => False.elim ((seed_nonneg _ _ hw s).not_gt bad.2))
  obtain ⟨i,_,hi⟩ := (sum_pos_iff_of_nonneg (s := univ) (fun i _ => show 0 ≤ (if side (left F) (right F) i=s ∧ target (left F) (right F) i=t then oriented w i else 0) by split_ifs <;> first | exact div_nonneg (hw _) (by norm_num) | rfl)).mp flowpos
  obtain ⟨e,b⟩ := i
  have ends : side (left F) (right F) (e,b) = s ∧ target (left F) (right F) (e,b) = t := by
    by_contra h'; simp [h'] at hi
  obtain ⟨a,c,he,_⟩ := hF e.val (List.mem_toFinset.mp e.property)
  have mem : Clause.pair a c ∈ F.formula := he ▸ List.mem_toFinset.mp e.property
  rcases ends with ⟨rfl,rfl⟩
  cases b
  · simpa [side,target,left,right,he,forbidden,partner] using (Relation.ReflTransGen.single (Arc.right mem))
  · simpa [side,target,left,right,he,forbidden,partner] using (Relation.ReflTransGen.single (Arc.left mem))

end TwoSAT.OracleWalk

end

section

namespace TwoSAT.Walk.Kernel

open Finset TwoSAT.Entropy

variable {S : Type} [Fintype S] [DecidableEq S]

/-- Finite geometric recursion. The base law distinguishes forced stops from discarded mass. -/
noncomputable def stopped (K : Kernel S) (η : ℝ) (base : S → S → ℝ) : ℕ → S → S → ℝ
  | 0 => base
  | h+1 => fun i j => η*(if i=j then 1 else 0) + (1-η)*∑ k, K.prob i k*K.stopped η base h k j

noncomputable def capped (K : Kernel S) (η : ℝ) := K.stopped η (fun i j => if i=j then 1 else 0)

theorem stopped_nonneg (K : Kernel S) {η : ℝ} (he : 0 ≤ η) (hu : η ≤ 1)
    {base : S → S → ℝ} (hb : ∀ i j, 0 ≤ base i j) (h : ℕ) (i j : S) : 0 ≤ K.stopped η base h i j := by
  induction h generalizing i with
  | zero => exact hb i j
  | succ h ih =>
    exact add_nonneg (mul_nonneg he (by split_ifs <;> norm_num)) (mul_nonneg (sub_nonneg.mpr hu)
      (sum_nonneg fun k _ => mul_nonneg (K.nonneg ..) (ih k)))

theorem stopped_mono (K : Kernel S) {η : ℝ} (hu : η ≤ 1) {f g : S → S → ℝ}
    (hb : ∀ i j, f i j ≤ g i j) (h : ℕ) (i j : S) : K.stopped η f h i j ≤ K.stopped η g h i j := by
  induction h generalizing i with
  | zero => exact hb i j
  | succ h ih =>
    exact add_le_add_right (mul_le_mul_of_nonneg_left (sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (ih k) (K.nonneg ..)) (sub_nonneg.mpr hu)) _

theorem stopped_sum (K : Kernel S) (η : ℝ) {base : S → S → ℝ} {r : ℝ} (hb : ∀ i, ∑ j, base i j = r)
    (h : ℕ) (i : S) : ∑ j, K.stopped η base h i j = 1-(1-r)*(1-η)^h := by
  induction h generalizing i with
  | zero => simp [stopped,hb]
  | succ h ih =>
    simp only [stopped,sum_add_distrib,← mul_sum,sum_ite_eq,mem_univ,if_true,mul_one]
    rw [sum_comm]
    simp only [← mul_sum,ih,← sum_mul,K.row,one_mul,pow_succ]
    ring

theorem capped_row (K : Kernel S) (η : ℝ) (h : ℕ) (i : S) : ∑ j, K.capped η h i j = 1 := by
  simpa only [capped,sub_self,zero_mul,sub_zero] using K.stopped_sum η
    (base := fun i j => if i=j then 1 else 0) (r := 1) (fun i => by simp) h i

theorem capped_nonneg (K : Kernel S) {η : ℝ} (he : 0 ≤ η) (hu : η ≤ 1) (h : ℕ) (i j : S) :
    0 ≤ K.capped η h i j := K.stopped_nonneg he hu (fun i j => by split_ifs <;> norm_num) h i j

private theorem endpoint_fixed (K : Kernel S) {η : ℝ} (hη : 0 < η) (hu : η < 1) (h : ℕ) :
    K.stopped η (K.endpoint η) h = K.endpoint η := by
  induction h with
  | zero => rfl
  | succ h ih =>
    funext i j; rw [stopped,ih]; exact (K.endpoint_rec hη hu i j).symm

omit [DecidableEq S] in
private theorem cap_error (p q : S → ℝ) (hq : ∀ i, 0 ≤ q i) (hle : ∀ i, q i ≤ p i)
    (sp : ∑ i, p i = 1) {r : ℝ} (sq : ∑ i, q i = 1-r) (e : S ≃ S) :
    affinity p (p ∘ e) ≤ affinity q (q ∘ e) + 2*√r := by
  let d i := p i-q i
  have hd (i) : 0 ≤ d i := sub_nonneg.mpr (hle i)
  have sd : ∑ i, d i = r := by simp [d,sum_sub_distrib,sq,sp]
  have hp (i) := (hq i).trans (hle i)
  have sr (i) : √(p i) ≤ √(q i)+√(d i) := by
    have hs := Real.sq_sqrt (hd i)
    dsimp [d] at hs ⊢
    nlinarith only [hs,Real.sq_sqrt (hp i),Real.sq_sqrt (hq i),Real.sqrt_nonneg (p i),
      Real.sqrt_nonneg (q i),Real.sqrt_nonneg (p i-q i),mul_nonneg (Real.sqrt_nonneg (q i)) (Real.sqrt_nonneg (p i-q i))]
  have one (i : S) : √(p i)*√(p (e i)) ≤
      √(q i)*√(q (e i)) + √(d i)*√(p (e i)) + √(p i)*√(d (e i)) := by
    linarith only [mul_le_mul_of_nonneg_right (sr i) (Real.sqrt_nonneg (p (e i))),
      mul_le_mul_of_nonneg_left (sr (e i)) (Real.sqrt_nonneg (q i)),
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hle i)) (Real.sqrt_nonneg (d (e i)))]
  have av := sum_le_sum (s := univ) (fun i _ => one i)
  rw [sum_add_distrib,sum_add_distrib] at av
  have l := affinity_le d (p ∘ e) hd (fun i => hp _)
  have m := affinity_le p (d ∘ e) hp (fun i => hd _)
  simp only [Function.comp_apply] at l m
  rw [e.sum_comp p,sp,sd,Real.sqrt_one,mul_one] at l
  rw [e.sum_comp d,sd,sp,Real.sqrt_one,one_mul] at m
  unfold affinity at *; simp only [Function.comp_apply] at *
  linarith only [av,l,m]

/-- Forcing a stop after h transitions loses at most twice the square root of the geometric tail. -/
theorem capped_affinity (K : Kernel S) {η : ℝ} (hη : 0 < η) (hu : η < 1) (h : ℕ) (i : S) (e : S ≃ S) :
    K.endpointAffinity η e i ≤ affinity (K.capped η h i) ((K.capped η h i) ∘ e) + 2*√((1-η)^h) := by
  let q := K.stopped η (fun _ _ => 0) h i
  have hq (j : S) : 0 ≤ q j := K.stopped_nonneg hη.le hu.le (fun _ _ => le_rfl) h i j
  have hle (j : S) : q j ≤ K.endpoint η i j := by
    have hh := K.stopped_mono hu.le (fun s t => K.endpoint_nonneg hη hu s t) h i j
    rwa [endpoint_fixed K hη hu] at hh
  have sq : ∑ j, q j = 1-(1-η)^h := by
    simpa using K.stopped_sum η (base := fun _ _ => 0) (r := 0) (fun _ => by simp) h i
  have hcap (j) : q j ≤ K.capped η h i j :=
    K.stopped_mono hu.le (fun s t => show (0:ℝ) ≤ (if s=t then 1 else 0) by split_ifs <;> norm_num) h i j
  apply (cap_error _ q hq hle (K.endpoint_row hη hu i) sq e).trans
  apply add_le_add_left _ _
  exact sum_le_sum fun j _ => mul_le_mul (Real.sqrt_le_sqrt (hcap j)) (Real.sqrt_le_sqrt (hcap (e j))) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end TwoSAT.Walk.Kernel

end

section

namespace TwoSAT.Sampler

open Finset TwoSAT.Walk

variable {n d : ℕ} {α : Type}

private def extendTree (j : ℕ) {q : ℕ} : Tree n d q → Tree n d (j+q)
  | .leaf b => .leaf b
  | .ask x i next => .ask x i (fun a => extendTree j (next a))

private theorem extendTree_run (j : ℕ) {q : ℕ} (o : Oracle n d) (t : Tree n d q) :
    (extendTree j t).run o = t.run o := by
  induction t with
  | leaf => rfl
  | ask x i next ih => exact ih (o x i)

theorem fixed (k : ℕ) (p : PMF α) : Cost (n := n) (d := d) k (fun _ => p) := by
  intro j g hg
  obtain ⟨trees,ht⟩ := Query.draw p hg
  rw [Nat.add_comm]
  refine ⟨trees.map (extendTree k),fun o => ?_⟩
  simpa only [PMF.map_comp,Function.comp_def,extendTree_run] using ht o

noncomputable def coin (a : ℝ) (h : 0 ≤ a) (hu : a ≤ 1) : PMF Bool :=
  ofMass (fun b => if b then a else 1-a) (fun b => by cases b <;> simp [h,sub_nonneg.mpr hu])
    (by simp)

theorem mass_coin (a : ℝ) (h hu) (b : Bool) : mass (coin a h hu) b = (if b then a else 1-a) :=
  mass_ofMass .. 

/-- Run at most h transitions, checking the geometric stop before each one. -/
noncomputable def walk (step : α → Oracle n d → PMF α) (a : ℝ) (h : 0 ≤ a) (hu : a ≤ 1) :
    ℕ → α → Oracle n d → PMF α
  | 0,s,_ => PMF.pure s
  | k+1,s,o => (coin a h hu).bind (fun b => if b then PMF.pure s else
      (step s o).bind (fun j => walk step a h hu k j o))

theorem walk_cost (step : α → Oracle n d → PMF α) (a : ℝ) (ha hu) (q : ℕ)
    (cost : ∀ s, Cost q (step s)) (k : ℕ) (s : α) : Cost (k*q) (walk step a ha hu k s) := by
  induction k generalizing s with
  | zero => simpa [walk] using fixed (n := n) (d := d) 0 (PMF.pure s)
  | succ k ih =>
    rw [Nat.succ_mul,Nat.add_comm (k*q) q]
    let f (b : Bool) (o : Oracle n d) := if b then PMF.pure s else (step s o).bind (fun j => walk step a ha hu k j o)
    have hb (b : Bool) : Cost (q+k*q) (f b) := by
      cases b
      · exact bind (cost s) ih
      · exact fixed _ _
    simpa only [Nat.zero_add,walk,f] using bind (j := 0) (k := q+k*q) (draw (coin a ha hu)) hb

theorem walk_mass [Fintype α] [DecidableEq α] (step : α → Oracle n d → PMF α) (a : ℝ) (ha hu)
    (o : Oracle n d) (P : Kernel α) (hP : ∀ s t, mass (step s o) t = P.prob s t) (k : ℕ) (s t : α) :
    mass (walk step a ha hu k s o) t = P.capped a k s t := by
  induction k generalizing s with
  | zero => simp [walk,Kernel.capped,Kernel.stopped,eq_comm]
  | succ k ih =>
    simp only [walk,mass_bind,Fintype.sum_bool,mass_coin,if_true,if_false,Bool.false_eq_true,
      Kernel.capped,Kernel.stopped,mass_pure,hP,ih]
    by_cases h : t=s
    · subst t; rfl
    · rw [if_neg h,if_neg (Ne.symm h)]

theorem walk_path (step : Literal (Fin n) → Oracle n d → PMF (Literal (Fin n))) (a : ℝ) (ha hu)
    (F : Input n d) (valid : ∀ s t, 0 < mass (step s F.oracle) t → Path F.formula s t)
    (k : ℕ) (s t : Literal (Fin n)) (h : 0 < mass (walk step a ha hu k s F.oracle) t) : Path F.formula s t := by
  induction k generalizing s with
  | zero =>
    by_cases he : t=s
    · subst t; exact .refl
    · simp [walk,mass_pure,he] at h
  | succ k ih =>
    by_cases he : t=s
    · subst t; exact .refl
    simp only [walk,mass_bind,Fintype.sum_bool,mass_coin,if_true,if_false,Bool.false_eq_true,mass_pure,he,mul_zero] at h
    have sumpos : 0 < ∑ j, mass (step s F.oracle) j * mass (walk step a ha hu k j F.oracle) t := by
      apply pos_of_mul_pos_right _ (sub_nonneg.mpr hu); linarith only [h]
    obtain ⟨j,_,pos⟩ := (sum_pos_iff_of_nonneg (fun j _ => mul_nonneg (mass_nonneg ..) (mass_nonneg ..))).mp sumpos
    exact (valid s j (pos_of_mul_pos_left pos (mass_nonneg ..))).trans (ih j (pos_of_mul_pos_right pos (mass_nonneg ..)))

end TwoSAT.Sampler

end

section

namespace TwoSAT.Collision

open Finset
open scoped BigOperators

/-- The finite second-moment inequality used in Lemma 6.3. -/
theorem secondMoment {Ω : Type*} [Fintype Ω] (μ Z : Ω → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hZ : ∀ i, 0 ≤ Z i) :
    (∑ i, μ i * Z i) ^ 2 ≤
      (∑ i, if 0 < Z i then μ i else 0) * ∑ i, μ i * Z i ^ 2 := by
  classical
  let f (i : Ω) := if 0 < Z i then √(μ i) else 0
  let g (i : Ω) := √(μ i) * Z i
  have hf (i) : f i ^ 2 = if 0 < Z i then μ i else 0 := by
    dsimp [f]; split_ifs <;> simp [Real.sq_sqrt (hμ i)]
  have hg (i) : g i ^ 2 = μ i * Z i ^ 2 := by simp [g, mul_pow, Real.sq_sqrt (hμ i)]
  have hfg (i) : f i * g i = μ i * Z i := by
    by_cases h : 0 < Z i
    · simp only [f, g, if_pos h, ← mul_assoc, Real.mul_self_sqrt (hμ i)]
    · simp [f, g, show Z i = 0 by linarith [hZ i]]
  simpa only [hfg, hf, hg] using sum_mul_sq_le_sq_mul_sq univ f g

/-- The numerical last step of Lemma 6.3. With affinity ≥ a, batch
size at least √N/a + 1/a² suffices for the stated second-moment estimate. -/
theorem quarter_of_moments {a A N M p m₂ : ℝ}
    (ha : 0 < a) (hA : a ≤ A) (hN : 0 ≤ N)
    (hM : √N / a + 1 / a ^ 2 ≤ M) (hp : 0 ≤ p)
    (hfirst : A ^ 2 ≤ p * m₂) (hsecond : m₂ ≤ A ^ 2 + 2/M + N/M^2) :
    1/4 ≤ p := by
  have hM₀ : 0 < M := by
    have : 0 ≤ √N / a := by positivity
    have : 0 < 1 / a^2 := by positivity
    linarith
  have hmass : 1 / a^2 ≤ M := by linarith [show 0 ≤ √N / a by positivity]
  have hcard : √N / a ≤ M := by linarith [show 0 < 1/a^2 by positivity]
  have hsmall : 1 ≤ M * a ^ 2 := (div_le_iff₀ (by positivity)).mp hmass
  have hroot : √N ≤ M*a := (div_le_iff₀ ha).mp hcard
  have hN' : N ≤ M^2*a^2 := by
    have hh := mul_self_le_mul_self (Real.sqrt_nonneg N) hroot
    rw [Real.mul_self_sqrt hN] at hh
    nlinarith
  have ht : 2/M ≤ 2*a^2 := (div_le_iff₀ hM₀).mpr (by nlinarith)
  have hu : N/M^2 ≤ a^2 := (div_le_iff₀ (sq_pos_of_pos hM₀)).mpr (by linarith)
  have hAA : a^2 ≤ A^2 := pow_le_pow_left₀ ha.le hA 2
  have he : m₂ ≤ 4*A^2 := by linarith
  have hp' := mul_le_mul_of_nonneg_left he hp
  by_contra! hh
  have hl := mul_lt_mul_of_pos_right hh (sq_pos_of_pos (ha.trans_le hA))
  nlinarith

end TwoSAT.Collision

end

section

namespace TwoSAT.Collision

open Finset
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {M : ℕ}

abbrev Samples (Ω : Type*) (M : ℕ) := (Fin M → Ω) × (Fin M → Ω)

noncomputable def joint (p q : Ω → ℝ) (v : Samples Ω M) := batch p v.1 * batch q v.2

noncomputable def tally (c : Ω → ℝ) (v : Samples Ω M) :=
  ∑ z, c z * (count v.1 z * count v.2 z)

private theorem tally_mean (p q c : Ω → ℝ) (hp : ∑ z, p z = 1) (hq : ∑ z, q z = 1) :
    mean (joint p q) (tally (M := M) c) = (M : ℝ)^2 * ∑ z, c z * (p z * q z) := by
  unfold tally joint
  rw [mean_sum, mul_sum]
  apply sum_congr rfl
  intro z _
  rw [mean_scale, independent_mean (batch p : (Fin M → Ω) → ℝ) (fun v => count v z)
    (batch q : (Fin M → Ω) → ℝ) (fun v => count v z), mean_count _ hp, mean_count _ hq]
  simp; ring

private theorem tally_sq (c : Ω → ℝ) (v : Samples Ω M) :
    tally c v ^ 2 = ∑ z, ∑ w, (c z * c w) *
      ((count v.1 z * count v.1 w) * (count v.2 z * count v.2 w)) := by
  simp only [sq, tally, sum_mul, mul_sum]
  apply sum_congr rfl; intro z _
  apply sum_congr rfl; intros; ring

private noncomputable def amp (p q : Ω → ℝ) (z : Ω) := √(p z * q z)
private noncomputable def coeff (p q : Ω → ℝ) (z : Ω) := (amp p q z)⁻¹

omit [Fintype Ω] [DecidableEq Ω] in
private theorem coeff_mass (p q : Ω → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (z : Ω) :
    coeff p q z * (p z * q z) = amp p q z := by
  have h : amp p q z ^ 2 = p z * q z := Real.sq_sqrt (mul_nonneg (hp _) (hq _))
  unfold coeff
  rw [← h]
  by_cases hz : amp p q z = 0
  · simp [hz]
  · field_simp

omit [Fintype Ω] in
private theorem entry_bound (p q : Ω → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (m d : ℝ) (hm : 0 ≤ m) (hd : 0 ≤ d) (z w : Ω) :
    (coeff p q z * coeff p q w) *
      ((d * p z * p w + (if z = w then m * p z else 0)) *
       (d * q z * q w + (if z = w then m * q z else 0))) ≤
    d^2 * amp p q z * amp p q w +
      (if w = z then d*m*(p z + q z) + m^2 else 0) := by
  by_cases h : z = w
  · subst w
    simp only [if_true]
    have hex : coeff p q z ^ 2 * (p z * q z) ≤ 1 := by
      rw [sq, mul_assoc, coeff_mass _ _ hp hq]
      by_cases hz : amp p q z = 0 <;> simp [coeff, hz]
    have hnn : 0 ≤ d*m*(p z + q z) + m^2 := by
      have := hp z; have := hq z; positivity
    calc
      _ = d^2 * (coeff p q z * (p z * q z))^2 +
          (d*m*(p z + q z) + m^2) * (coeff p q z^2 * (p z*q z)) := by ring
      _ ≤ _ := by rw [coeff_mass _ _ hp hq]; nlinarith only [mul_le_mul_of_nonneg_left hex hnn]
  · simp only [if_neg h, if_neg (Ne.symm h), add_zero]
    rw [← coeff_mass _ _ hp hq z, ← coeff_mass _ _ hp hq w]
    exact le_of_eq (by ring)

private theorem raw_second (p q : Ω → ℝ) (hp : ∀ z, 0 ≤ p z) (hq : ∀ z, 0 ≤ q z)
    (hsp : ∑ z, p z = 1) (hsq : ∑ z, q z = 1) (hM : 1 ≤ M) :
    mean (joint p q) (fun v : Samples Ω M => tally (coeff p q) v ^ 2) ≤
      (M : ℝ)^4 * (∑ z, amp p q z)^2 + 2*M^3 + (Fintype.card Ω : ℝ)*M^2 := by
  let m : ℝ := M
  let d := m*(m-1)
  have hm : (1 : ℝ) ≤ m := by dsimp [m]; exact_mod_cast hM
  have hd : 0 ≤ d := mul_nonneg (by linarith) (by linarith)
  have hdm : d ≤ m^2 := by dsimp [d]; nlinarith
  have hpair (z w : Ω) := independent_mean (batch p : (Fin M → Ω) → ℝ)
    (fun v => count v z * count v w) (batch q : (Fin M → Ω) → ℝ) (fun v => count v z * count v w)
  unfold joint
  simp_rw [tally_sq, mean_sum, mean_scale, hpair, mean_count_product _ hsp,
    mean_count_product _ hsq, Fintype.card_fin]
  calc
    _ ≤ ∑ z, ∑ w, (d^2 * amp p q z * amp p q w +
        (if w = z then d*m*(p z + q z) + m^2 else 0)) := by
      exact sum_le_sum fun z _ => sum_le_sum fun w _ => entry_bound p q hp hq m d (by linarith) hd z w
    _ = d^2*(∑ z, amp p q z)^2 + 2*d*m + (Fintype.card Ω : ℝ)*m^2 := by
      simp only [sum_add_distrib, sum_ite_eq', mem_univ, if_true, ← mul_sum,
        ← sum_mul, sum_const, card_univ, nsmul_eq_mul, hsp, hsq]
      ring
    _ ≤ _ := by
      change _ ≤ m^4 * _ + 2*m^3 + _*m^2
      nlinarith only [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hdm 2)
        (sq_nonneg (∑ z, amp p q z)), mul_le_mul_of_nonneg_right hdm (show 0 ≤ m by linarith)]

private theorem tally_zero (c : Ω → ℝ) (v : Samples Ω M) (none : ¬ ∃ i j, v.1 i = v.2 j) :
    tally c v = 0 := by
  apply sum_eq_zero
  intro z _
  by_cases x : ∃ i, v.1 i = z
  · obtain ⟨i, hi⟩ := x
    have h (j) : v.2 j ≠ z := fun hj => none ⟨i, j, hi.trans hj.symm⟩
    simp [count, h]
  · have h (i) : v.1 i ≠ z := fun hi => x ⟨i, hi⟩
    simp [count, h]

/-- Lemma 6.3, with C* = 1. The summand is the product probability of a
pair of independent batches; the event is the existence of a shared value. -/
theorem two_distribution_collision (p q : Ω → ℝ) (hp : ∀ z, 0 ≤ p z) (hq : ∀ z, 0 ≤ q z)
    (hsp : ∑ z, p z = 1) (hsq : ∑ z, q z = 1) {a : ℝ} (ha : 0 < a)
    (hA : a ≤ ∑ z, √(p z * q z)) {N : ℕ} (hcard : Fintype.card Ω ≤ N)
    (hsize : √(N : ℝ) / a + 1/a^2 ≤ M) :
    (1/4 : ℝ) ≤ ∑ v : Samples Ω M, if ∃ i j, v.1 i = v.2 j then joint p q v else 0 := by
  let m : ℝ := M
  have hm : 0 < m := by
    have : 0 ≤ √(N : ℝ) / a := by positivity
    have : 0 < 1 / a^2 := by positivity
    dsimp [m]; linarith
  have hM : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (by intro h; simp [m, h] at hm)
  let A := ∑ z, amp p q z
  let Z (v : Samples Ω M) := (1 / m^2) * tally (coeff p q) v
  let μ : Samples Ω M → ℝ := joint p q
  have hμ (v : Samples Ω M) : 0 ≤ μ v :=
    mul_nonneg (prod_nonneg fun i _ => hp (v.1 i)) (prod_nonneg fun i _ => hq (v.2 i))
  have hcount (v : Fin M → Ω) (z : Ω) : 0 ≤ count v z := by
    apply sum_nonneg; intro i _; split_ifs <;> norm_num
  have hZ (v) : 0 ≤ Z v := by
    dsimp [Z]
    exact mul_nonneg (by positivity) (sum_nonneg fun z _ =>
      mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (mul_nonneg (hcount _ z) (hcount _ z)))
  have hfirst : mean μ Z = A := by
    rw [show mean μ Z = (1/m^2)*mean (joint p q) (tally (M := M) (coeff p q)) from mean_scale _ _ _,
      tally_mean p q _ hsp hsq]
    simp only [coeff_mass p q hp hq]
    change 1/m^2 * (m^2*A) = A
    field_simp
  have hsecond : mean μ (fun v => Z v ^ 2) ≤ A^2 + 2/m + (N : ℝ)/m^2 := by
    have he := raw_second p q hp hq hsp hsq hM
    change mean μ (fun v => tally (coeff p q) v ^ 2) ≤ m^4 * A^2 + 2*m^3 + (Fintype.card Ω : ℝ)*m^2 at he
    simp only [Z, mul_pow, mean_scale]
    calc
      _ ≤ (1/m^2)^2 * (m^4*A^2 + 2*m^3 + (Fintype.card Ω : ℝ)*m^2) :=
        mul_le_mul_of_nonneg_left he (sq_nonneg _)
      _ = A^2 + 2/m + (Fintype.card Ω : ℝ)/m^2 := by field_simp
      _ ≤ _ := by gcongr
  let prob := ∑ v, if 0 < Z v then μ v else 0
  have hprob : 0 ≤ prob := sum_nonneg fun v _ => by split_ifs <;> first | exact hμ _ | rfl
  have hCS : (mean μ Z)^2 ≤ prob * mean μ (fun v => Z v ^ 2) := secondMoment μ Z hμ hZ
  rw [hfirst] at hCS
  apply (quarter_of_moments ha hA (Nat.cast_nonneg N) hsize hprob hCS hsecond).trans
  apply sum_le_sum
  intro v _
  by_cases h : ∃ i j, v.1 i = v.2 j
  · simp only [if_pos h]
    split_ifs <;> first | rfl | exact hμ _
  · simp [Z, tally_zero _ _ h, h]

end TwoSAT.Collision

end

section

namespace TwoSAT.Amplification

open Finset
open scoped BigOperators

/-- If the mean two-way affinity is at least b, seeds with affinity at
least b/2 contribute enough mass for the four independent batches in §6.2. -/
theorem trial_bound {S : Type*} [Fintype S] (μ a p q : S → ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hμ : ∀ s, 0 ≤ μ s) (sumμ : ∑ s, μ s = 1) (ha : ∀ s, a s ≤ 1)
    (havg : b ≤ ∑ s, μ s * a s) (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (hgood : ∀ s, b / 2 ≤ a s → 1 / 4 ≤ p s ∧ 1 / 4 ≤ q s) :
    b / 32 ≤ ∑ s, μ s * (p s * q s) := by
  classical
  let good (s : S) := if b/2 ≤ a s then μ s else 0
  have hmean : ∑ s, μ s * a s ≤ (∑ s, good s) + (∑ s, μ s) * (b/2) := by
    rw [sum_mul, ← sum_add_distrib]
    apply sum_le_sum
    intro s _
    by_cases h : b/2 ≤ a s
    · simp only [good, if_pos h]
      nlinarith [mul_le_mul_of_nonneg_left (ha s) (hμ s), mul_nonneg (hμ s) hb]
    · simp only [good, if_neg h, zero_add]
      exact mul_le_mul_of_nonneg_left (le_of_not_ge h) (hμ s)
  have hsuccess : (∑ s, good s) * (1/16) ≤ ∑ s, μ s * (p s * q s) := by
    rw [sum_mul]
    apply sum_le_sum
    intro s _
    by_cases h : b/2 ≤ a s
    · simp only [good, if_pos h]
      apply mul_le_mul_of_nonneg_left _ (hμ s)
      obtain ⟨h₁, h₂⟩ := hgood s h
      have hh := mul_le_mul h₁ h₂ (by norm_num : (0 : ℝ) ≤ 1/4) (hp s)
      linarith
    · simp only [good, if_neg h, zero_mul]
      exact mul_nonneg (hμ s) (mul_nonneg (hp s) (hq s))
  rw [sumμ, one_mul] at hmean
  linarith

/-- Independent repetitions miss with probability (1-p)^R. The trial count
in the paper ensures R p ≥ 4. -/
theorem miss_bound {p : ℝ} {R : ℕ} (hp : p ≤ 1) (hR : 4 ≤ (R : ℝ) * p) :
    (1 - p) ^ R ≤ 1 / 16 := by
  have h : 1 - p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
  calc
    _ ≤ Real.exp (-p) ^ R := pow_le_pow_left₀ (sub_nonneg.mpr hp) h _
    _ = Real.exp ((R : ℝ) * (-p)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (-4) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ _ := by
      rw [Real.exp_neg]
      have h16 : (16 : ℝ) ≤ Real.exp 4 := by
        calc
          (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
          _ ≤ Real.exp 1 ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _
          _ = Real.exp 4 := by norm_num [← Real.exp_nat_mul]
      simpa [one_div] using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 16) h16)

end TwoSAT.Amplification

end

section

namespace TwoSAT.Collision

open Finset
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The two batches here use the same endpoint distribution. -/
noncomputable def matchProb (p : Ω → ℝ) (e : Ω ≃ Ω) (M : ℕ) : ℝ :=
  ∑ v : Samples Ω M, if ∃ i j, v.1 i = e (v.2 j) then joint p p v else 0

noncomputable def endpointAffinity (p : Ω → ℝ) (e : Ω ≃ Ω) : ℝ :=
  ∑ z, √(p z * p (e z))

omit [DecidableEq Ω] in
private theorem joint_one (p : Ω → ℝ) (hp : ∑ z, p z = 1) (M : ℕ) :
    ∑ v : Samples Ω M, joint p p v = 1 := by
  simp only [joint, Fintype.sum_prod_type, ← mul_sum, batch_mass p hp, mul_one]

omit [Fintype Ω] [DecidableEq Ω] in
private theorem joint_pos (p : Ω → ℝ) (hp : ∀ i, 0 ≤ p i) {M : ℕ} (v : Samples Ω M) :
    0 ≤ joint p p v := mul_nonneg (prod_nonneg fun _ _ => hp _) (prod_nonneg fun _ _ => hp _)

theorem matchProb_bounds (p : Ω → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ z, p z = 1)
    (e : Ω ≃ Ω) (M : ℕ) : 0 ≤ matchProb p e M ∧ matchProb p e M ≤ 1 := by
  constructor
  · exact sum_nonneg fun v _ => by split_ifs <;> first | exact joint_pos _ hp _ | rfl
  · rw [← joint_one p hs M]
    exact sum_le_sum fun v _ => by split_ifs <;> first | rfl | exact joint_pos _ hp _

theorem matchProb_quarter (p : Ω → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ z, p z = 1)
    (e : Ω ≃ Ω) (he : Function.Involutive e) {a : ℝ} (ha : 0 < a)
    (hA : a ≤ endpointAffinity p e) {M N : ℕ} (hcard : Fintype.card Ω ≤ N)
    (hm : √(N : ℝ)/a + 1/a^2 ≤ M) : 1/4 ≤ matchProb p e M := by
  let f (v : Samples Ω M) :=
    if ∃ i j, v.1 i = v.2 j then joint p (p ∘ e) v else 0
  have h : 1/4 ≤ ∑ v, f v :=
    two_distribution_collision p (p ∘ e) hp (fun i => hp _) hs ((e.sum_comp p).trans hs)
      ha hA hcard hm
  let E : Samples Ω M ≃ Samples Ω M :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.piCongrRight fun _ => e)
  rw [← E.sum_comp f] at h
  have hinv (x : Ω) : e (e x) = x := he x
  simpa [f, E, joint, batch, matchProb, Function.comp_def, hinv] using h

omit [DecidableEq Ω] in
private theorem affinity_le_one (p : Ω → ℝ) (hp : ∀ z, 0 ≤ p z) (hs : ∑ z, p z = 1)
    (e : Ω ≃ Ω) : endpointAffinity p e ≤ 1 := by
  have h := Real.sum_sqrt_mul_sqrt_le univ hp (fun z => hp (e z))
  have h' := (e.sum_comp p).trans hs
  simpa [endpointAffinity, Real.sqrt_mul (hp _), hs, h'] using h

/-- One random seed and four independent endpoint batches, as in §6.2.
Given two-way affinity b, the two simultaneous collisions have probability ≥ b/32. -/
theorem four_batch_bound (e : Ω ≃ Ω) (he : Function.Involutive e) (μ : Ω → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (sμ : ∑ s, μ s = 1) (p : Ω → Ω → ℝ)
    (hp : ∀ s z, 0 ≤ p s z) (sp : ∀ s, ∑ z, p s z = 1) {b : ℝ} (hb : 0 < b)
    (havg : b ≤ ∑ s, μ s * min (endpointAffinity (p s) e) (endpointAffinity (p (e s)) e))
    {M N : ℕ} (hcard : Fintype.card Ω ≤ N) (hm : √(N : ℝ)/(b/2) + 1/(b/2)^2 ≤ M) :
    b/32 ≤ ∑ s, μ s * (matchProb (p s) e M * matchProb (p (e s)) e M) := by
  apply TwoSAT.Amplification.trial_bound μ _ _ _ hb.le hμ sμ _ havg
  · exact fun s => (matchProb_bounds _ (hp _) (sp _) e M).1
  · exact fun s => (matchProb_bounds _ (hp _) (sp _) e M).1
  · intro s hs
    obtain ⟨h₁, h₂⟩ := le_min_iff.mp hs
    exact ⟨matchProb_quarter _ (hp _) (sp _) e he (by positivity) h₁ hcard hm,
      matchProb_quarter _ (hp _) (sp _) e he (by positivity) h₂ hcard hm⟩
  · exact fun s => (min_le_left _ _).trans (affinity_le_one _ (hp s) (sp s) e)

end TwoSAT.Collision

end

section

namespace TwoSAT.Sampler

open Finset TwoSAT.Collision

variable {S : Type} [Fintype S] [DecidableEq S] {n d : ℕ}

noncomputable def matchLaw (e : S ≃ S) (p : PMF S) (M : ℕ) : PMF Bool := by
  classical
  exact (copies p M).bind fun x => (copies p M).map (fun y => decide (∃ i j, x i = e (y j)))

theorem match_mass (e : S ≃ S) (p : PMF S) (M : ℕ) :
    mass (matchLaw e p M) true = matchProb (mass p) e M := by
  classical
  rw [matchLaw,mass_bind,matchProb,Fintype.sum_prod_type]
  apply sum_congr rfl; intro x _
  rw [mass_map,mul_sum]
  apply sum_congr rfl; intro y _
  by_cases h : ∃ i j, x i=e (y j) <;> simp [h,copies_mass,joint,batch]

omit [Fintype S] in
theorem match_cost (e : S ≃ S) {p : Oracle n d → PMF S} {k : ℕ} (hp : Cost k p) (M : ℕ) :
    Cost (M*k+M*k) (fun o => matchLaw e (p o) M) := by
  classical
  let f (x y : Fin M → S) := decide (∃ i j, x i=e (y j))
  have h (x : Fin M → S) := map (copies_cost hp M) (f x)
  exact bind (copies_cost hp M) h

noncomputable def both (p q : PMF Bool) := p.bind (fun b => q.map (fun a => b && a))

theorem both_mass (p q : PMF Bool) : mass (both p q) true = mass p true*mass q true := by
  simp [both,mass_bind,mass_map]

theorem both_cost {p q : Oracle n d → PMF Bool} {j k : ℕ} (hp : Cost j p) (hq : Cost k q) :
    Cost (j+k) (fun o => both (p o) (q o)) :=
  bind hp (fun b => map hq (fun a => b && a))

noncomputable def trial (e : S ≃ S) (seed : PMF S) (p : S → PMF S) (M : ℕ) : PMF Bool :=
  seed.bind fun s => both (matchLaw e (p s) M) (matchLaw e (p (e s)) M)

theorem trial_mass (e : S ≃ S) (seed : PMF S) (p : S → PMF S) (M : ℕ) :
    mass (trial e seed p M) true =
      ∑ s, mass seed s * (matchProb (mass (p s)) e M * matchProb (mass (p (e s))) e M) := by
  simp only [trial,mass_bind,both_mass,match_mass]

omit [Fintype S] in
theorem trial_cost (e : S ≃ S) (seed : PMF S) (p : S → Oracle n d → PMF S) {k : ℕ}
    (hp : ∀ s, Cost k (p s)) (M : ℕ) :
    Cost (4*M*k) (fun o => trial e seed (fun s => p s o) M) := by
  have branch s := both_cost (match_cost e (hp s) M) (match_cost e (hp (e s)) M)
  have h := bind (draw (n := n) (d := d) seed) branch
  convert h using 1
  · ring
  · rfl

noncomputable def repeatTrials (p : PMF Bool) : ℕ → PMF Bool
  | 0 => PMF.pure false
  | r+1 => p.bind fun b => (repeatTrials p r).map (fun a => b || a)

theorem repeat_cost {p : Oracle n d → PMF Bool} {j : ℕ} (hp : Cost j p) (R : ℕ) :
    Cost (R*j) (fun o => repeatTrials (p o) R) := by
  induction R with
  | zero => simpa [repeatTrials] using fixed (n := n) (d := d) 0 (PMF.pure false)
  | succ r ih =>
    rw [Nat.succ_mul,Nat.add_comm (r*j) j]
    exact bind hp (fun b => map ih (fun a => b || a))

theorem bool_sum (p : PMF Bool) : mass p false + mass p true = 1 := by
  simpa [Fintype.sum_bool,add_comm] using mass_sum p

theorem repeat_mass (p : PMF Bool) (R : ℕ) : mass (repeatTrials p R) true = 1-(1-mass p true)^R := by
  have miss (r : ℕ) : mass (repeatTrials p r) false = (mass p false)^r := by
    induction r with
    | zero => simp [repeatTrials]
    | succ r ih => simp [repeatTrials,mass_bind,mass_map,ih,pow_succ,mul_comm]
  have val : mass p false = 1-mass p true := by linarith only [bool_sum p]
  linarith only [bool_sum (repeatTrials p R),show mass (repeatTrials p R) false = (1-mass p true)^R by rw [miss,val]]

/-- A positive-mass collision has two positive-mass endpoints related by complementation. -/
theorem match_witness (e : S ≃ S) (p : PMF S) (M : ℕ) (h : 0 < matchProb (mass p) e M) :
    ∃ z, 0 < mass p z ∧ 0 < mass p (e z) := by
  classical
  have hpos (v : Samples S M) : 0 ≤ (if ∃ i j, v.1 i=e (v.2 j) then joint (mass p) (mass p) v else 0) := by
    split_ifs
    · exact mul_nonneg (prod_nonneg (fun _ _ => mass_nonneg ..)) (prod_nonneg (fun _ _ => mass_nonneg ..))
    · rfl
  obtain ⟨v,_,hv⟩ := (sum_pos_iff_of_nonneg (fun v _ => hpos v)).mp h
  split_ifs at hv with he
  · obtain ⟨i,j,he⟩ := he
    have each (x : Fin M → S) (h : 0 < batch (mass p) x) (l : Fin M) : 0 < mass p (x l) := by
      by_contra! hn
      have hz := hn.antisymm (mass_nonneg ..)
      have zero : batch (mass p) x = 0 := prod_eq_zero (mem_univ l) hz
      linarith
    refine ⟨v.2 j,each _ (pos_of_mul_pos_right hv (prod_nonneg (fun _ _ => mass_nonneg ..))) j,?_⟩
    rw [← he]
    exact each _ (pos_of_mul_pos_left hv (prod_nonneg (fun _ _ => mass_nonneg ..))) i
  · linarith

end TwoSAT.Sampler

end

section

namespace TwoSAT.Budgets

theorem ceil_scaled {a x : ℝ} (ha : 0 ≤ a) (hx : 1 ≤ x) :
    (⌈a*x⌉₊ : ℝ) ≤ (a+1)*x := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hax : 0 ≤ a * x := mul_nonneg ha hx0
  have h1 : (⌈a*x⌉₊ : ℝ) < a * x + 1 := by
    exact_mod_cast Nat.ceil_lt_add_one hax
  have h2 : a * x + 1 ≤ (a + 1) * x := by
    have : a * x + 1 ≤ a * x + x := by linarith
    calc
      a * x + 1 ≤ a * x + x := this
      _ = (a + 1) * x := by ring
  linarith

theorem small_power (x ν : ℝ) (hx : 1 ≤ x) (_hν : 0 ≤ ν) (hu : ν ≤ 1/2) :
    x^(ν/2) * x^(ν/2) ≤ x^((1:ℝ)/2+ν/2) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hu' : ν/2 + ν/2 ≤ (1:ℝ)/2 + ν/2 := by linarith
  calc
    x ^ (ν/2) * x ^ (ν/2) = x ^ (ν/2 + ν/2) := (Real.rpow_add hx0 _ _).symm
    _ ≤ x ^ ((1:ℝ)/2 + ν/2) := Real.rpow_le_rpow_of_exponent_le hx hu'


theorem batch_ceiling (x ν c : ℝ) (hx : 1 ≤ x) (hν : 0 ≤ ν) (hu : ν ≤ 1/2) (hc : 0 < c) :
    let inv := x^(ν/2)/c
    (⌈√x*(2*inv)+(2*inv)^2⌉₊ : ℝ) ≤ (2/c+4/c^2+1) * x^((1:ℝ)/2+ν/2) := by
  intro inv
  have hx0 : 0 < x := by linarith
  have hinv : 0 ≤ inv := by dsimp [inv]; positivity
  let Y := x^((1:ℝ)/2+ν/2)
  have hY : 1 ≤ Y := Real.one_le_rpow hx (by linarith)
  have one : √x*(2*inv) = 2/c*Y := by
    dsimp [inv,Y]; rw [Real.sqrt_eq_rpow,Real.rpow_add hx0]; ring
  have two : (2*inv)^2 ≤ 4/c^2*Y := by
    have he : (2*inv)^2 = 4/c^2 * (x^(ν/2) * x^(ν/2)) := by dsimp [inv]; ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (small_power x ν hx hν hu) (by positivity)
  have ceiling := (Nat.ceil_lt_add_one (show 0 ≤ √x*(2*inv)+(2*inv)^2 by positivity)).le
  change _ ≤ _ * Y
  linarith only [ceiling,one,two,hY]

theorem endpoint_budget (x ν c : ℝ) (hx : 1 ≤ x) (hν : 0 ≤ ν) (hu : ν ≤ 1/2) (hc : 0 < c) :
    let inv := x^(ν/2)/c
    let R := ⌈128*inv⌉₊
    let M := ⌈√x*(2*inv)+(2*inv)^2⌉₊
    (4*R*M : ℕ) ≤ (4*(128/c+1)*(2/c+4/c^2+1)) * x^((1:ℝ)/2+ν) := by
  intro inv R M
  have hx0 : 0 < x := by linarith
  have hR : (R : ℝ) ≤ (128/c+1)*x^(ν/2) := by
    have eq : 128*inv = (128/c)*x^(ν/2) := by dsimp [inv]; ring
    change (⌈128*inv⌉₊ : ℝ) ≤ _
    rw [eq]
    exact ceil_scaled (by positivity) (Real.one_le_rpow hx (by linarith))
  have hM : (M : ℝ) ≤ _ := batch_ceiling x ν c hx hν hu hc
  have hh := mul_le_mul hR hM (Nat.cast_nonneg M) (by positivity)
  have powers : x^(ν/2)*x^((1:ℝ)/2+ν/2) = x^((1:ℝ)/2+ν) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  push_cast
  calc
    _ = 4*((R : ℝ)*M) := by ring
    _ ≤ 4*(((128/c+1)*x^(ν/2))*((2/c+4/c^2+1)*x^((1:ℝ)/2+ν/2))) :=
      mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = 4*(128/c+1)*(2/c+4/c^2+1) * (x^(ν/2)*x^((1:ℝ)/2+ν/2)) := by ring
    _ = _ := by rw [powers]

end TwoSAT.Budgets

end

section

namespace TwoSAT.Budgets

/-- A deterministic cap for every walk costs at most a quadratic logarithmic factor. -/
theorem geometric_cap {γ c ν x : ℝ} (hγ : 0 < γ) (hu : γ ≤ 1) (hc : 0 < c) (hν : 0 ≤ ν)
    (hx : 1 ≤ x) :
    let A := 4/c+ν+1
    let L := 1+Real.log x
    let η := γ/L
    let H := ⌈2*A*L^2/γ⌉₊
    (H : ℝ) ≤ (2*A/γ+1)*L^2 ∧ 2*√((1-η)^H) ≤ c/2*x^(-ν/2) := by
  intro A L η H
  have lx := Real.log_nonneg hx
  have hx0 : 0 < x := by linarith
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 < L := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hη : 0 < η := div_pos hγ hL0
  have hη1 : η ≤ 1 := (div_le_self hγ.le hL).trans hu
  constructor
  · have ceil := Nat.ceil_lt_add_one (show 0 ≤ 2*A*L^2/γ by positivity)
    change (⌈2*A*L^2/γ⌉₊ : ℝ) ≤ _
    nlinarith only [ceil,one_le_pow₀ hL (n := 2),show 2*A*L^2/γ = (2*A/γ)*L^2 by ring]
  · have lo : 2*A*L^2/γ ≤ (H:ℝ) := Nat.le_ceil _
    have hit : 2*A*L ≤ η*H := by
      have h := mul_le_mul_of_nonneg_left lo hη.le
      apply le_trans _ h
      dsimp [η]; field_simp; rfl
    have target : 2*Real.log (4/c)+ν*Real.log x ≤ η*H := by
      have logle := Real.log_le_sub_one_of_pos (show 0 < 4/c by positivity)
      apply le_trans _ hit
      dsimp [A,L]
      nlinarith only [logle,mul_nonneg (show 0 ≤ 4/c by positivity) lx,mul_nonneg hν lx,lx,hν]
    let z := Real.exp (-(Real.log (4/c))-ν/2*Real.log x)
    have hz : 0 ≤ z := (Real.exp_pos _).le
    have base : 1-η ≤ Real.exp (-η) := by linarith only [Real.add_one_le_exp (-η)]
    have pp := pow_le_pow_left₀ (sub_nonneg.mpr hη1) base H
    rw [← Real.exp_nat_mul] at pp
    have cmp : (1-η)^H ≤ z^2 := by
      dsimp [z]; rw [← Real.exp_nat_mul]
      apply pp.trans (Real.exp_le_exp.mpr _)
      push_cast; linarith only [target]
    have bound := (Real.sqrt_le_sqrt cmp).trans_eq (Real.sqrt_sq hz)
    have eqn : z = c/4*x^(-ν/2) := by
      dsimp [z]; rw [Real.rpow_def_of_pos hx0,Real.exp_sub,Real.exp_neg,Real.exp_log (by positivity)]
      rw [show Real.log x*(-ν/2) = -(ν/2*Real.log x) by ring,Real.exp_neg]
      field_simp
    rw [eqn] at bound
    linarith only [bound]

end TwoSAT.Budgets

end

section

namespace TwoSAT.Budgets

theorem card_literals (V : Type) [Fintype V] : Fintype.card (Literal V) = 2*Fintype.card V := by
  let e : Literal V ≃ V × Bool := ⟨fun l => (l.var,l.sign),fun p => ⟨p.1,p.2⟩,fun _ => rfl,fun _ => rfl⟩
  simpa [Nat.mul_comm] using Fintype.card_congr e

theorem size_bound (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 0 ≤ p) :
    let x := (Fintype.card (Option (Literal (Fin n))) : ℝ)
    x^p * (1+Real.log x)^2 ≤
      (3^p*(1+Real.log 3)^2)*(n:ℝ)^p*(1+Real.log n)^2 := by
  intro x
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0:ℝ) < n := by exact_mod_cast hn
  have eqn : x = 2*(n:ℝ)+1 := by simp [x,Fintype.card_option,card_literals]
  have hx : 0 < x := by rw [eqn]; positivity
  have le : x ≤ 3*n := by linarith only [eqn,h1]
  have powle := Real.rpow_le_rpow hx.le le hp
  rw [Real.mul_rpow (by norm_num) h0.le] at powle
  have logle := Real.log_le_log hx le
  rw [Real.log_mul (by norm_num) h0.ne'] at logle
  have logn := Real.log_nonneg h1
  have log3 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)
  have l1 : 0 ≤ 1+Real.log x := by
    have := Real.log_nonneg (show 1 ≤ x by linarith only [eqn,h0]); linarith
  have l2 : 1+Real.log x ≤ (1+Real.log 3)*(1+Real.log n) := by
    nlinarith only [logle,mul_nonneg logn log3]
  have both := mul_le_mul powle (pow_le_pow_left₀ l1 l2 2) (sq_nonneg _) (by positivity)
  exact both.trans_eq (by ring)

end TwoSAT.Budgets

end

section

namespace TwoSAT.OracleWalk

open Finset TwoSAT.Walk TwoSAT.Sampler TwoSAT.ClauseLaw TwoSAT.LocalWeights

variable {n d : ℕ}

noncomputable def uniform (n : ℕ) (hn : 0 < n) : PMF (L n) :=
  ofMass (fun _ => 1/(2*(n:ℝ))) (fun _ => by positivity) (by
    have h : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [L,Budgets.card_literals]; field_simp)

theorem uniform_mass (hn : 0 < n) (s : L n) : Sampler.mass (uniform n hn) s = 1/(2*n) := mass_ofMass ..

noncomputable def oneTrial (hn : 0 < n) (T H M : ℕ) (η : ℝ) (he : 0 ≤ η) (hu : η ≤ 1) (o : Oracle n d) :=
  trial flipPerm (uniform n hn) (fun s => walk (step T) η he hu H s o) M

theorem trial_queries (hn : 0 < n) (T H M q : ℕ) (η : ℝ) (he hu)
    (hf : ∀ (u v : L n), Query.Bounded q (localWeight d T u v)) :
    Cost (d := d) (4*M*(H*(d*(1+q)))) (oneTrial hn T H M η he hu) :=
  trial_cost flipPerm (uniform n hn) _ (walk_cost _ η he hu _ (step_cost T q hf) H) M

theorem trial_sound (hn : 0 < n) (T H M : ℕ) (η : ℝ) (he hu) (F : Input n d)
    (hF : Reduction.Exact F) (sat : Satisfiable F.formula) :
    mass (oneTrial hn T H M η he hu F.oracle) true = 0 := by
  let p s := walk (step T) η he hu H s F.oracle
  have sound (s t : L n) := walk_path (step T) η he hu F (positive_step_path T F hF) H s t
  have one (s : L n) : Collision.matchProb (mass (p s)) flipPerm M *
      Collision.matchProb (mass (p s.flip)) flipPerm M = 0 := by
    have pos (z : L n) := (Collision.matchProb_bounds _ (mass_nonneg (p z)) (mass_sum (p z)) flipPerm M).1
    by_contra h'
    obtain ⟨a,b⟩ := mul_ne_zero_iff.mp h'
    obtain ⟨z,hz,hz'⟩ := match_witness flipPerm (p s) M ((pos s).lt_of_ne' a)
    obtain ⟨t,ht,ht'⟩ := match_witness flipPerm (p s.flip) M ((pos s.flip).lt_of_ne' b)
    exact fourWalks (sound s z hz) (sound s z.flip hz') (sound s.flip t ht) (sound s.flip t.flip ht') sat
  rw [oneTrial,trial_mass]
  apply sum_eq_zero; intro s _
  change Sampler.mass (uniform n hn) s * (Collision.matchProb (Sampler.mass (p s)) flipPerm M * Collision.matchProb (Sampler.mass (p s.flip)) flipPerm M) = 0
  rw [one s,mul_zero]

/-- Transfer two-way endpoint affinity through the finite cap and the uniform choice of seed. -/
theorem trial_far (hn : 0 < n) (T H M : ℕ) {η a b : ℝ} (he : 0 < η) (hu : η < 1)
    (ha : 0 < a) (hb : 0 < b) (F : Input n d) (hF : Reduction.Exact F) (W : ℝ) (hW : 0 < W)
    (π : Edges F → ℝ) (hπ : ∀ e, 0 < π e) (eqπ : ∀ e, π e = clauseWeight d T F.oracle e.val/W)
    (sp : ∑ e, π e = 1) (seedBound : ∀ s, a*seed (left F) (right F) π s ≤ 1/(2*n))
    (high : b ≤ twoWayMean (forward (left F) (right F) π (fun e => (hπ e).le)).lazy
      (seed (left F) (right F) π) η) (tail : 2*√((1-η)^H) ≤ b/2)
    {N : ℕ} (card : Fintype.card (L n) ≤ N) (batch : √(N:ℝ)/((a*b/2)/2)+1/((a*b/2)/2)^2 ≤ M) :
    a*b/2/32 ≤ mass (oneTrial hn T H M η he.le hu.le F.oracle) true := by
  let P := (forward (left F) (right F) π (fun e => (hπ e).le)).lazy
  let μ := seed (left F) (right F) π
  let p s := walk (step T) η he.le hu.le H s F.oracle
  have stepEq (s t : L n) : mass (step T s F.oracle) t = P.prob s t := by
    have heq : π = _ := funext eqπ
    subst π
    exact normalized_step T F hF W hW s t
  have law (s t : L n) : mass (p s) t = P.capped η H s t := walk_mass _ η he.le hu.le F.oracle P stepEq H s t
  let c s := Collision.endpointAffinity (mass (p s)) flipPerm
  have close (s : L n) : P.endpointAffinity η flipPerm s ≤ c s + b/2 := by
    apply (P.capped_affinity he hu H s flipPerm).trans
    apply add_le_add _ tail
    unfold c Collision.endpointAffinity Entropy.affinity
    simp only [← law,Function.comp_apply,Real.sqrt_mul (mass_nonneg ..),le_refl]
  let m (s : L n) := min (c s) (c s.flip)
  have hm (s : L n) : 0 ≤ m s := le_min (sum_nonneg fun _ _ => Real.sqrt_nonneg _) (sum_nonneg fun _ _ => Real.sqrt_nonneg _)
  have mu := seed_nonneg (left F) (right F) (fun e => (hπ e).le)
  have sumμ : ∑ s, μ s = 1 := (seed_total ..).trans sp
  have cmp (s : L n) : μ s*min (P.endpointAffinity η flipPerm s) (P.endpointAffinity η flipPerm s.flip) ≤
      μ s*m s + μ s*(b/2) := by
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (mu s)
    exact (min_le_min (close s) (close s.flip)).trans_eq (min_add_add_right ..)
  have hh := high.trans (sum_le_sum (s := univ) (fun s _ => cmp s))
  rw [sum_add_distrib,← sum_mul,sumμ,one_mul] at hh
  have hh' : b/2 ≤ ∑ s, μ s*m s := by linarith only [hh]
  have sub := sum_le_sum (s := univ) (fun s _ => mul_le_mul_of_nonneg_right (seedBound s) (hm s))
  have goalmean : a*b/2 ≤ ∑ s, Sampler.mass (uniform n hn) s*m s := by
    simp only [uniform_mass]
    have scaled := mul_le_mul_of_nonneg_left hh' ha.le
    simp only [mul_assoc,← mul_sum] at sub
    change a*(∑ s, μ s*m s) ≤ 1/(2*(n:ℝ)) * ∑ i, m i at sub
    rw [← mul_sum]
    linarith only [scaled,sub]
  rw [oneTrial,trial_mass]
  exact Collision.four_batch_bound flipPerm Literal.flip_flip (Sampler.mass (uniform n hn)) (mass_nonneg _) (mass_sum _)
    (fun s => mass (p s)) (fun s => mass_nonneg _) (fun s => mass_sum _) (by positivity) goalmean card batch

end TwoSAT.OracleWalk

end

section

namespace TwoSAT.Reduction

/-- The query-complexity assertion of §6.3 restricted to E2SAT. -/
def ExactClaim : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ ε ν : ℝ, 0 < ε → 0 < ν → ν < 1 / 2 →
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ (q : ℕ) (alg : PMF (Tree n d q)),
        (q : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ν) * (1 + Real.log n) ^ k ∧
        ∀ F : Input n d, Exact F →
          (Satisfiable F.formula → rejection alg F = 0) ∧
          (ε * d * n ≤ distance F.formula → (2 / 3 : ENNReal) ≤ rejection alg F)

private theorem scale_bound {n k : ℕ} (hn : 1 ≤ n) {C a : ℝ} (hC : 0 < C) :
    C * ((n + n : ℕ) : ℝ) ^ a * (1 + Real.log ((n + n : ℕ) : ℝ)) ^ k ≤
      (C * 2 ^ a * (1 + Real.log 2) ^ k) * (n : ℝ) ^ a * (1 + Real.log n) ^ k := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hlog := Real.log_nonneg hn'
  have htwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hle : 1 + (Real.log 2 + Real.log n) ≤ (1 + Real.log 2) * (1 + Real.log n) := by
    nlinarith [mul_nonneg htwo hlog]
  have hh : ((n + n : ℕ) : ℝ) = 2 * n := by push_cast; ring
  rw [hh, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn0.le,
    Real.log_mul (by norm_num) hn0.ne']
  calc
    _ ≤ C * (2 ^ a * (n : ℝ) ^ a) * ((1 + Real.log 2) * (1 + Real.log n)) ^ k := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

/-- Section 6.4 transfers the exact-clause tester to arbitrary bounded-degree
2CNFs, including unit clauses, tautologies and arbitrary null-slot locations. -/
theorem mainClaim_of_exact (h : ExactClaim) : MainClaim := by
  intro d hd ε ν hε hν hν'
  obtain ⟨C, k, hC, H⟩ := h (d + d) (by omega) (ε / 4) ν (by positivity) hν hν'
  let a := (1 : ℝ) / 2 + ν
  refine ⟨C * 2 ^ a * (1 + Real.log 2) ^ k, k, ?_, ?_⟩
  · have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  intro n hn
  obtain ⟨q, alg, hq, htest⟩ := H (n + n) (by omega)
  refine ⟨q, alg.map simulate, hq.trans (scale_bound hn hC), ?_⟩
  intro F
  have result := htest (doubledInput F) (doubled_exact F)
  have prob : rejection (alg.map simulate) F = rejection alg (doubledInput F) :=
    congrArg (fun μ : PMF Bool => μ true) (simulate_distribution F.oracle alg)
  rw [prob]
  refine ⟨fun hs => result.1 (doubled_satisfiable F hs), ?_⟩
  intro hfar
  apply result.2
  rw [doubled_distance]
  push_cast
  linarith only [hfar]

end TwoSAT.Reduction

end

section

namespace TwoSAT

open Finset TwoSAT.Walk TwoSAT.LocalWeights TwoSAT.OracleWalk TwoSAT.Budgets

/-- The local weighted-walk collision tester for formulas with two distinct variables per clause. -/
theorem verified_exact_tester_bound : Reduction.ExactClaim := by
  intro d hd ε ν hε hν hν1
  let ε' := min ε 1
  have hε' : 0 < ε' := lt_min hε zero_lt_one
  obtain ⟨T,k,γ,c,a,hγ,hγ1,hc,ha,cost,analysis⟩ := local_law d hd hε' (min_le_right ..) hν
  let c' := a*c/2
  have hC : 0 < c' := by dsimp [c']; positivity
  let A := 4/c+ν+1
  let D := d*(1+k)
  let p := (1:ℝ)/2+ν
  let B := 4*(128/c'+1)*(2/c'+4/c'^2+1)
  let G := 2*A/γ+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hG : 0 < G := by dsimp [G,A]; positivity
  have hD : 0 < (D:ℝ) := by exact_mod_cast (Nat.mul_pos hd (by omega : 0 < 1+k))
  let C := B*G*D*(3^p*(1+Real.log 3)^2)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have log3 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)
  refine ⟨C,2,by dsimp [C]; positivity,?_⟩
  intro n hn
  let N := Fintype.card (Option (Literal (Fin n)))
  let x := (N:ℝ)
  have hx : 1 ≤ x := by simp [x,N,Fintype.card_option]
  have hx0 : 0 < x := by linarith
  let Lg := 1+Real.log x
  let η := γ/Lg
  have lg1 : 1 ≤ Lg := by dsimp [Lg]; linarith only [Real.log_nonneg hx]
  have he : 0 < η := div_pos hγ (by linarith)
  have hu : η < 1 := (div_le_self hγ.le lg1).trans_lt (by linarith)
  let H := ⌈2*A*Lg^2/γ⌉₊
  let inv := x^(ν/2)/c'
  let R := ⌈128*inv⌉₊
  let M := ⌈√x*(2*inv)+(2*inv)^2⌉₊
  let b := c*x^(-ν/2)
  have hb : 0 < b := mul_pos hc (Real.rpow_pos_of_pos hx0 _)
  have cap := geometric_cap hγ (hγ1.trans (by norm_num)) hc hν.le hx
  change (H:ℝ) ≤ G*Lg^2 ∧ 2*√((1-η)^H) ≤ c/2*x^(-ν/2) at cap
  have capTail : 2*√((1-η)^H) ≤ b/2 := cap.2.trans_eq (by dsimp [b]; ring)
  have budgets := endpoint_budget x ν c' hx hν.le hν1.le hC
  change ((4*R*M : ℕ) : ℝ) ≤ B*x^p at budgets
  let q := R*(4*M*(H*D))
  let law := oneTrial (d := d) hn T H M η he.le hu.le
  have trialCost : Sampler.Cost (4*M*(H*D)) law := trial_queries hn T H M k η he.le hu.le (cost n)
  obtain ⟨alg,run⟩ := Sampler.finish (Sampler.repeat_cost trialCost R)
  refine ⟨q,alg,?_,?_⟩
  · have counts := mul_le_mul budgets cap.1 (by positivity : (0:ℝ) ≤ H) (by positivity : 0 ≤ B*x^p)
    have changeSize := size_bound n hn p hp
    change x^p*Lg^2 ≤ (3^p*(1+Real.log 3)^2)*(n:ℝ)^p*(1+Real.log n)^2 at changeSize
    have scale := mul_le_mul_of_nonneg_left changeSize (show 0 ≤ B*G*(D:ℝ) by positivity)
    have count := mul_le_mul_of_nonneg_right counts hD.le
    dsimp only [q,C]
    push_cast at count ⊢
    linarith only [count,scale]
  intro F hF
  have identity : rejection alg F = (Sampler.repeatTrials (law F.oracle) R) true :=
    congrArg (fun dist : PMF Bool => dist true) (run F.oracle)
  rw [identity]
  let P := law F.oracle
  constructor
  · intro sat
    have zero : Sampler.mass P true = 0 := trial_sound hn T H M η he.le hu.le F hF sat
    have prob := Sampler.repeat_mass P R
    rw [zero,sub_zero,one_pow,sub_self] at prob
    exact ((ENNReal.toReal_eq_zero_iff _).mp prob).resolve_right ((Sampler.repeatTrials P R).apply_ne_top true)
  · intro far
    have eff : ε'*(d:ℝ)*n ≤ distance F.formula := by
      apply le_trans _ far
      gcongr
      exact min_le_left .. 
    obtain ⟨πpos,sπ,hW,seed,high⟩ := analysis n hn F hF eff
    have inverse : 1/(a*b/2) = inv := by
      dsimp [b,inv,c']; rw [neg_div,Real.rpow_neg hx0.le]
      field_simp
    have batch : √(N:ℝ)/((a*b/2)/2)+1/((a*b/2)/2)^2 ≤ (M:ℝ) := by
      apply le_trans _ (Nat.le_ceil (√x*(2*inv)+(2*inv)^2))
      rw [← inverse]; dsimp only [x]; apply le_of_eq; ring
    have card : Fintype.card (OracleWalk.L n) ≤ N := by simp [N,Fintype.card_option]
    have trialP : a*b/2/32 ≤ Sampler.mass P true :=
      trial_far hn T H M he hu ha hb F hF _ hW _ πpos (fun _ => rfl) sπ seed high capTail card batch
    have count : 4 ≤ (R:ℝ)*Sampler.mass P true := by
      have hR : 128*inv ≤ (R:ℝ) := Nat.le_ceil _
      have hh := mul_le_mul hR trialP (show 0 ≤ a*b/2/32 by positivity) (Nat.cast_nonneg R)
      apply le_trans _ hh
      rw [← inverse]; field_simp; norm_num
    have atmost : Sampler.mass P true ≤ 1 := by linarith only [Sampler.bool_sum P,Sampler.mass_nonneg P false]
    have miss := Amplification.miss_bound atmost count
    have win : (2/3:ℝ) ≤ Sampler.mass (Sampler.repeatTrials P R) true := by
      rw [Sampler.repeat_mass]; linarith only [miss]
    apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top (by norm_num) (by norm_num)) ((Sampler.repeatTrials P R).apply_ne_top true)).mp
    simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat,Sampler.mass] using win
end TwoSAT

end

open TwoSAT in
theorem solution :
  ∀ (d : ℕ), 1 ≤ d → ∀ ε ν : ℝ, 0 < ε → 0 < ν → ν < 1 / 2 →
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ (q : ℕ) (alg : PMF (Tree n d q)),
        (q : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ν) * (1 + Real.log n) ^ k ∧
        ∀ F : Input n d, Reduction.Exact F →
          (Satisfiable F.formula → rejection alg F = 0) ∧
          (ε * d * n ≤ distance F.formula → (2 / 3 : ENNReal) ≤ rejection alg F) := TwoSAT.verified_exact_tester_bound
