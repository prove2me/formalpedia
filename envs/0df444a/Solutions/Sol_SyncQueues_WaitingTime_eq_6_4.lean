-- Prove2me | solution 1 for SyncQueues.WaitingTime.eq_6_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T14:36:28.404466+00:00
-- url     : https://prove2.me/submissions/c1de5015-4e9c-4ddc-b66f-90f43d7f7d04

import Mathlib
import Definitions.Def_SyncQueues_WaitingTime_BranchingTree
import Definitions.Def_SyncQueues_WaitingTime_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SyncQEq64

lemma meas_expPDF (r : ℝ) : Measurable (exponentialPDF r) :=
  (measurable_exponentialPDFReal r).ennreal_ofReal

lemma lintegral_exp_neg_expMeasure {r β : ℝ} (hr : 0 < r) (hβ : 0 < β) :
    ∫⁻ t, ENNReal.ofReal (Real.exp (-(β * t))) ∂(expMeasure r) = ENNReal.ofReal (r / (r + β)) := by
  have hrb : 0 < r + β := by linarith
  have h1 : (expMeasure r) = volume.withDensity (exponentialPDF r) := rfl
  rw [h1, lintegral_withDensity_eq_lintegral_mul _ (meas_expPDF r)
    (by fun_prop)]
  have key : ∀ t, (exponentialPDF r * fun t => ENNReal.ofReal (Real.exp (-(β * t)))) t =
      ENNReal.ofReal (r / (r + β)) * exponentialPDF (r + β) t := by
    intro t
    simp only [Pi.mul_apply]
    rcases lt_or_ge t 0 with ht | ht
    · rw [exponentialPDF_of_neg ht, exponentialPDF_of_neg ht]; simp
    · rw [exponentialPDF_of_nonneg ht, exponentialPDF_of_nonneg ht,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : Real.exp (-((r + β) * t)) = Real.exp (-(r * t)) * Real.exp (-(β * t)) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]; field_simp
  simp_rw [key]
  rw [lintegral_const_mul _ (meas_expPDF _), lintegral_exponentialPDF_eq_one hrb,
    mul_one]


lemma edge_lintegral {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') (B : Measure ℝ) [SFinite B]
    {lamStar β : ℝ} (hl : 0 < lamStar) (hβ : 0 < β) (X Y : Ω' → ℝ) (hX : Measurable X)
    (hY : Measurable Y) (hmap : P'.map (fun ω => (X ω, Y ω)) = B.prod (expMeasure lamStar)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (β * (X ω - Y ω))) ∂P' =
      (∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂B) * ENNReal.ofReal (lamStar / (lamStar + β)) := by
  have hg : Measurable (fun z : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (β * z.1)) * ENNReal.ofReal (Real.exp (-(β * z.2)))) := by
    fun_prop
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (β * (X ω - Y ω))) =
      (fun z : ℝ × ℝ => ENNReal.ofReal (Real.exp (β * z.1)) * ENNReal.ofReal (Real.exp (-(β * z.2))))
        (X ω, Y ω) := by
    intro ω
    simp only
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  simp_rw [hpt]
  haveI : IsProbabilityMeasure (expMeasure lamStar) := isProbabilityMeasure_expMeasure hl
  rw [← lintegral_map hg (hX.prodMk hY), hmap,
    lintegral_prod_mul (f := fun x => ENNReal.ofReal (Real.exp (β * x)))
      (g := fun t => ENNReal.ofReal (Real.exp (-(β * t)))) (by fun_prop) (by fun_prop),
    lintegral_exp_neg_expMeasure hl hβ]

instance pieceLaw_finite {m : ℕ} (Bm : Measure (Fin m → ℝ)) [IsProbabilityMeasure Bm] :
    IsFiniteMeasure (SyncQueues.WaitingTime.pieceLaw Bm) := by
  constructor
  unfold SyncQueues.WaitingTime.pieceLaw
  have h1 : ∀ i : Fin m, (Bm.map (fun x => x i)) Set.univ = 1 := fun i => by
    rw [Measure.map_apply (measurable_pi_apply i) MeasurableSet.univ]; simp
  rw [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply]
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · rw [ENNReal.inv_mul_cancel (by exact_mod_cast h.ne') (by simp)]; simp


lemma pathSum_exp {m : ℕ} {Ω' : Type*} (χ τ : List (Fin m) → Ω' → ℝ) {β : ℝ} {r : ℕ}
    (v : Fin r → Fin m) (ω : Ω') :
    ENNReal.ofReal (Real.exp (β * SyncQueues.WaitingTime.pathSum χ τ (List.ofFn v) ω)) =
      ∏ l ∈ (Finset.range r).image (fun k => (List.ofFn v).take (k + 1)),
        ENNReal.ofReal (Real.exp (β * (χ l ω - τ l ω))) := by
  unfold SyncQueues.WaitingTime.pathSum
  rw [Finset.prod_image]
  · rw [List.length_ofFn, Finset.mul_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  · intro a ha b hb hab
    have := congrArg List.length hab
    simp only [List.length_take, List.length_ofFn] at this
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    omega

end SyncQEq64

open SyncQueues.WaitingTime

theorem solution {m : ℕ} (hm : 0 < m) {lam : ℝ} (hlam : 0 < lam)
    (Bm : Measure (Fin m → ℝ)) [IsProbabilityMeasure Bm] (hBm : ∀ᵐ x ∂Bm, ∀ i, 0 ≤ x i)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (χ τ : List (Fin m) → Ω' → ℝ) (htree : IsLimitTree P' (pieceLaw Bm) (lam * m) χ τ)
    {β : ℝ} (hβ : 0 < β) (r : ℕ) :
    ∫⁻ ω, ∑ v : Fin r → Fin m,
        ENNReal.ofReal (Real.exp (β * pathSum χ τ (List.ofFn v) ω)) ∂P' =
      rho Bm lam β ^ r := by
  obtain ⟨hmeas, hind, hlaw⟩ := htree
  have hls : 0 < lam * (m : ℝ) := mul_pos hlam (by exact_mod_cast hm)
  set c : ℝ≥0∞ := (∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂(pieceLaw Bm)) *
    ENNReal.ofReal (lam * m / (lam * m + β)) with hc
  let X : List (Fin m) → Ω' → ℝ≥0∞ := fun l ω => ENNReal.ofReal (Real.exp (β * (χ l ω - τ l ω)))
  have hXm : ∀ l, Measurable (X l) := fun l => by
    have h1 := (hmeas l).1; have h2 := (hmeas l).2
    fun_prop
  have hXi : iIndepFun X P' := by
    have := hind.comp (fun _ (z : ℝ × ℝ) => ENNReal.ofReal (Real.exp (β * (z.1 - z.2))))
      (fun _ => by fun_prop)
    exact this
  have hXl : ∀ l, ∫⁻ ω, X l ω ∂P' = c := fun l =>
    SyncQEq64.edge_lintegral P' (pieceLaw Bm) hls hβ (χ l) (τ l) (hmeas l).1 (hmeas l).2 (hlaw l)
  have hv : ∀ v : Fin r → Fin m,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (β * pathSum χ τ (List.ofFn v) ω)) ∂P' = c ^ r := by
    intro v
    simp_rw [SyncQEq64.pathSum_exp χ τ v]
    rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ X hXi hXm]
    simp only [hXl, Finset.prod_const]
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    have := congrArg List.length hab
    simp only [List.length_take, List.length_ofFn] at this
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    omega
  rw [lintegral_finset_sum _ (fun v _ => by
    have : ∀ l, Measurable (χ l) := fun l => (hmeas l).1
    have : ∀ l, Measurable (τ l) := fun l => (hmeas l).2
    unfold pathSum
    fun_prop)]
  simp only [hv, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul]
  unfold rho
  rw [hc, Nat.cast_pow, ← mul_pow, mul_assoc]
