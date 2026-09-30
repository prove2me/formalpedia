-- Prove2me | solution 1 for RobustMeanCov.Projection.exists_isotropic_lift
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T22:02:40.469679+00:00
-- url     : https://prove2.me/submissions/ae011982-948b-4699-bac4-416f728ce964

import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder


namespace RobustMeanCov.Projection

theorem lift_sum_aux {ι E : Type*} [Fintype ι] [MeasurableSpace E] (ζ : Measure ℝ)
    (w : ENNReal) (hw : w ≠ ⊤) (F : ι → ℝ → E) (hF : ∀ p, Measurable (F p))
    (g : E → ℝ) (hg : Measurable g) (h : ∀ p, Integrable (fun t => g (F p t)) ζ) :
    Integrable g (∑ p, w • ζ.map (F p)) ∧
      ∫ x, g x ∂(∑ p, w • ζ.map (F p)) = w.toReal * ∑ p, ∫ t, g (F p t) ∂ζ := by
  have hI : ∀ p, Integrable g (w • ζ.map (F p)) := by
    intro p
    refine Integrable.smul_measure ?_ hw
    exact (integrable_map_measure hg.aestronglyMeasurable (hF p).aemeasurable).2 (h p)
  refine ⟨integrable_finsetSum_measure.2 fun p _ => hI p, ?_⟩
  rw [integral_finsetSum_measure fun p _ => hI p, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_smul_measure, integral_map (hF p).aemeasurable hg.aestronglyMeasurable,
    smul_eq_mul]

theorem exists_isotropic_lift_core {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) (hy : ⟪y, y⟫ = 1)
    (ζ : Measure ℝ) (hζ : ζ ∈ RobustMeanCov.Shared.MeanVarClass 0 1) :
    ∃ Q ∈ MeanCovClass (0 : EuclideanSpace ℝ (Fin n)) (1 : Matrix (Fin n) (Fin n) ℝ),
      Q.map (fun Z => ⟪y, Z⟫) = ζ := by
  obtain ⟨hprob, hL2, hmean, hvar⟩ := hζ
  simp only [sub_zero] at hvar
  have hyy : ∑ k, y k * y k = 1 := by
    rw [← hy, PiLp.inner_apply]
    exact Finset.sum_congr rfl fun k _ => by simp; try ring
  have hn : n ≠ 0 := by
    rintro rfl; simp at hyy
  have hint1 : Integrable (fun t : ℝ => t) ζ := hL2.integrable one_le_two
  have hint2 : Integrable (fun t : ℝ => t ^ 2) ζ := hL2.integrable_sq
  set s : ℝ := Real.sqrt n with hs
  have hs2 : s * s = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  let c : Fin n × Bool → EuclideanSpace ℝ (Fin n) := fun p =>
    (if p.2 then s else -s) • (EuclideanSpace.single p.1 (1 : ℝ) - y p.1 • y)
  let F : Fin n × Bool → ℝ → EuclideanSpace ℝ (Fin n) := fun p t => t • y + c p
  have hF : ∀ p, Measurable (F p) := fun p => by fun_prop
  have hcoord : ∀ p t i, F p t i = t * y i + (if p.2 then s else -s) *
      ((if p.1 = i then 1 else 0) - y p.1 * y i) := by
    intro p t i
    rcases p with ⟨k, _ | _⟩ <;> by_cases h : k = i
    all_goals first
      | (subst h; simp [F, c])
      | simp [F, c, h, Ne.symm h]
  have hcsum : ∀ i, ∑ p : Fin n × Bool, (if p.2 then s else -s) *
      ((if p.1 = i then 1 else 0) - y p.1 * y i) = 0 := by
    intro i
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, neg_mul, add_neg_cancel,
      Finset.sum_const_zero]
  have hcprod : ∀ i j, ∑ p : Fin n × Bool, (if p.2 then s else -s) *
      ((if p.1 = i then 1 else 0) - y p.1 * y i) * ((if p.2 then s else -s) *
      ((if p.1 = j then 1 else 0) - y p.1 * y j)) =
      2 * n * ((if i = j then 1 else 0) - y i * y j) := by
    intro i j
    rw [Fintype.sum_prod_type]
    have : ∀ k : Fin n, ∑ b : Bool, (if b then s else -s) *
        ((if k = i then 1 else 0) - y k * y i) * ((if b then s else -s) *
        ((if k = j then 1 else 0) - y k * y j)) =
        2 * n * (((if k = i then 1 else 0) - y k * y i) * ((if k = j then 1 else 0) - y k * y j)) := by
      intro k
      rw [Fintype.sum_bool]; simp only [if_true, Bool.false_eq_true, if_false]
      rw [← hs2]; ring
    rw [Finset.sum_congr rfl fun k _ => this k, ← Finset.mul_sum]
    congr 1
    have e : ∀ k : Fin n, ((if k = i then (1:ℝ) else 0) - y k * y i) *
        ((if k = j then 1 else 0) - y k * y j) =
        (if k = i then (if k = j then 1 else 0) else 0) - (if k = i then y k * y j else 0)
         - (if k = j then y k * y i else 0) + y k * y k * (y i * y j) := by
      intro k; split_ifs <;> ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hyy]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    split_ifs with hij
    · subst hij; ring
    · ring
  set w : ENNReal := ((2 * n : ℕ) : ENNReal)⁻¹ with hw
  have hwtop : w ≠ ⊤ := by
    rw [hw, ENNReal.inv_ne_top]; exact_mod_cast (by omega : 2 * n ≠ 0)
  have hwr : w.toReal = (2 * n : ℝ)⁻¹ := by
    rw [hw, ENNReal.toReal_inv]; simp
  have hcard : (Finset.univ : Finset (Fin n × Bool)).card = 2 * n := by
    simp [Finset.card_univ, mul_comm]
  -- the measure
  refine ⟨∑ p, w • ζ.map (F p), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · constructor
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, smul_eq_mul]
    simp_rw [Measure.map_apply (hF _) MeasurableSet.univ, Set.preimage_univ, measure_univ,
      mul_one]
    rw [Finset.sum_const, hcard, nsmul_eq_mul, hw]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast (by omega : 2 * n ≠ 0)) (ENNReal.natCast_ne_top _)
  · intro i
    have hm : Measurable (fun R : EuclideanSpace ℝ (Fin n) => R i) := by fun_prop
    rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
    refine (lift_sum_aux ζ w hwtop F hF _ (by fun_prop) fun p => ?_).1
    simp_rw [hcoord]
    have := ((hint2.const_mul (y i ^ 2)).add (hint1.const_mul (2 * y i *
      ((if p.2 then s else -s) * ((if p.1 = i then 1 else 0) - y p.1 * y i))))).add
      (integrable_const (((if p.2 then s else -s) * ((if p.1 = i then 1 else 0) - y p.1 * y i)) ^ 2))
    exact this.congr (ae_of_all _ fun t => by simp only [Pi.add_apply]; ring)
  · intro i
    have hm : Measurable (fun R : EuclideanSpace ℝ (Fin n) => R i) := by fun_prop
    have hI : ∀ p, Integrable (fun t => F p t i) ζ := by
      intro p; simp_rw [hcoord]
      exact (hint1.mul_const _).add (integrable_const _)
    rw [(lift_sum_aux ζ w hwtop F hF _ hm hI).2]
    simp_rw [hcoord]
    have : ∀ p : Fin n × Bool, ∫ t, t * y i + (if p.2 then s else -s) *
        ((if p.1 = i then 1 else 0) - y p.1 * y i) ∂ζ = (if p.2 then s else -s) *
        ((if p.1 = i then 1 else 0) - y p.1 * y i) := by
      intro p
      rw [integral_add (hint1.mul_const _) (integrable_const _), integral_mul_const, hmean,
        integral_const]
      simp
    rw [Finset.sum_congr rfl fun p _ => this p, hcsum]
    simp
  · intro i j
    have hm : Measurable (fun R : EuclideanSpace ℝ (Fin n) => (R i - (0 : EuclideanSpace ℝ (Fin n)) i)
        * (R j - (0 : EuclideanSpace ℝ (Fin n)) j)) := by fun_prop
    have key : ∀ p : Fin n × Bool, ∀ a b : ℝ,
        Integrable (fun t : ℝ => (t * y i + a) * (t * y j + b)) ζ ∧
        ∫ t : ℝ, (t * y i + a) * (t * y j + b) ∂ζ = y i * y j + a * b := by
      intro p a b
      have e : (fun t : ℝ => (t * y i + a) * (t * y j + b)) =
          fun t => (y i * y j) * t ^ 2 + (y i * b + a * y j) * t + a * b := by
        funext t; ring
      rw [e]
      have h1 := hint2.const_mul (y i * y j)
      have h2 := hint1.const_mul (y i * b + a * y j)
      refine ⟨(h1.add h2).add (integrable_const _), ?_⟩
      beta_reduce
      rw [integral_add (f := fun t : ℝ => y i * y j * t ^ 2 + (y i * b + a * y j) * t)
        (g := fun _ => a * b) (h1.add h2) (integrable_const _), integral_add h1 h2,
        integral_const_mul, integral_const_mul, hvar, hmean, integral_const]
      simp
    have hI : ∀ p, Integrable (fun t => (F p t i - (0 : EuclideanSpace ℝ (Fin n)) i) *
        (F p t j - (0 : EuclideanSpace ℝ (Fin n)) j)) ζ := by
      intro p; simp_rw [hcoord]; simpa using (key p _ _).1
    rw [(lift_sum_aux ζ w hwtop F hF _ hm hI).2]
    simp_rw [hcoord]
    simp only [PiLp.zero_apply, sub_zero]
    rw [Finset.sum_congr rfl fun p _ => (key p _ _).2, Finset.sum_add_distrib, hcprod,
      Finset.sum_const, hcard, nsmul_eq_mul, hwr, Matrix.one_apply]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
    push_cast
    split_ifs <;> ring
  · ext A hA
    rw [Measure.map_apply (by fun_prop) hA, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, smul_eq_mul]
    have hpre : ∀ p, (F p) ⁻¹' ((fun Z : EuclideanSpace ℝ (Fin n) => ⟪y, Z⟫) ⁻¹' A) = A := by
      intro p
      ext t
      simp only [Set.mem_preimage, F, c, inner_add_right, inner_smul_right, hy, inner_sub_right,
        EuclideanSpace.inner_single_right]
      simp at *
    have hmA : MeasurableSet ((fun Z : EuclideanSpace ℝ (Fin n) => ⟪y, Z⟫) ⁻¹' A) :=
      (by fun_prop : Measurable fun Z : EuclideanSpace ℝ (Fin n) => ⟪y, Z⟫) hA
    have hq : ∀ p, ζ.map (F p) ((fun Z : EuclideanSpace ℝ (Fin n) => ⟪y, Z⟫) ⁻¹' A) = ζ A := by
      intro p; rw [Measure.map_apply (hF p) hmA, hpre p]
    simp only [hq]
    rw [Finset.sum_const, hcard, nsmul_eq_mul, ← mul_assoc, hw,
      ENNReal.mul_inv_cancel (by exact_mod_cast (by omega : 2 * n ≠ 0)) (ENNReal.natCast_ne_top _),
      one_mul]

end RobustMeanCov.Projection

open RobustMeanCov.Projection


theorem solution {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) (hy : ⟪y, y⟫ = 1)
    (ζ : Measure ℝ) (hζ : ζ ∈ RobustMeanCov.Shared.MeanVarClass 0 1) :
    ∃ Q ∈ MeanCovClass (0 : EuclideanSpace ℝ (Fin n)) (1 : Matrix (Fin n) (Fin n) ℝ),
      Q.map (fun Z => ⟪y, Z⟫) = ζ := by
  exact exists_isotropic_lift_core y hy ζ hζ
