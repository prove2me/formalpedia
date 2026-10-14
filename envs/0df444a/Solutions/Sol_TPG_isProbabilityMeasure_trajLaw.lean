-- Prove2me | solution 1 for TPG.isProbabilityMeasure_trajLaw
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:07:35.159903+00:00
-- url     : https://prove2.me/submissions/d71aa80b-2ca3-45ad-9182-71816a3d52fe

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Markov
import Theorems.Thm_TPG_integral_trajLaw

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

namespace TPG_FB_Prob

/-- A sum over tuples of length `n + 1` splits into a sum over the first `n` entries and the
last entry. -/
lemma sum_snoc {α : Type} [Fintype α] {M : Type} [AddCommMonoid M] (n : ℕ)
    (f : (Fin (n + 1) → α) → M) :
    ∑ x, f x = ∑ x : Fin n → α, ∑ a : α, f (Fin.snoc x a) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => α)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

lemma sum_snoc₂ {α β : Type} [Fintype α] [Fintype β] {M : Type} [AddCommMonoid M] (n : ℕ)
    (f : (Fin (n + 1) → α) → (Fin (n + 1) → β) → M) :
    ∑ x, ∑ z, f x z
      = ∑ x : Fin n → α, ∑ z : Fin n → β, ∑ a : α, ∑ b : β, f (Fin.snoc x a) (Fin.snoc z b) := by
  rw [sum_snoc]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm, sum_snoc]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_comm]

lemma sum_bool_ite (θ : ℝ) : ∑ b : Bool, (if b then θ else 1 - θ) = 1 := by
  simp

variable {S : Type} [Fintype S]

lemma pathWeight_zero (E : Env S) (q : ℕ → ℝ) (x : Fin 0 → S) (z : Fin 0 → Bool) :
    E.pathWeight 0 q x z = 1 := by
  simp [Env.pathWeight]

lemma pathWeight_one (E : Env S) (q : ℕ → ℝ) (x : Fin (0 + 1) → S) (z : Fin (0 + 1) → Bool) :
    E.pathWeight (0 + 1) q x z
      = E.ρ (x (Fin.last 0)) * (if z (Fin.last 0) then q 0 else 1 - q 0) := by
  simp [Env.pathWeight]

/-- Recursion for the path weight when one more time step is appended. -/
lemma pathWeight_snoc (E : Env S) (n : ℕ) (q : ℕ → ℝ) (x : Fin (n + 1) → S)
    (z : Fin (n + 1) → Bool) (a : S) (b : Bool) :
    E.pathWeight (n + 1 + 1) q (Fin.snoc x a) (Fin.snoc z b)
      = E.pathWeight (n + 1) q x z * E.P n (z (Fin.last n)) (x (Fin.last n)) a
          * (if b then q (n + 1) else 1 - q (n + 1)) := by
  classical
  have h1 : (∏ t : Fin (n + 1 + 1),
        if (t : ℕ) = 0 then E.ρ ((Fin.snoc x a : Fin (n + 1 + 1) → S) t) else 1)
      = ∏ t : Fin (n + 1), if (t : ℕ) = 0 then E.ρ (x t) else 1 := by
    rw [Fin.prod_univ_castSucc]
    simp
  have h3 : (∏ t : Fin (n + 1 + 1),
        if (Fin.snoc z b : Fin (n + 1 + 1) → Bool) t then q (t : ℕ) else 1 - q (t : ℕ))
      = (∏ t : Fin (n + 1), if z t then q (t : ℕ) else 1 - q (t : ℕ))
          * (if b then q (n + 1) else 1 - q (n + 1)) := by
    rw [Fin.prod_univ_castSucc]
    simp
  have h2 : (∏ s : Fin (n + 1 + 1), ∏ t : Fin (n + 1 + 1),
        if (s : ℕ) + 1 = (t : ℕ) then
          E.P (s : ℕ) ((Fin.snoc z b : Fin (n + 1 + 1) → Bool) s)
            ((Fin.snoc x a : Fin (n + 1 + 1) → S) s) ((Fin.snoc x a : Fin (n + 1 + 1) → S) t)
        else 1)
      = (∏ s : Fin (n + 1), ∏ t : Fin (n + 1),
          if (s : ℕ) + 1 = (t : ℕ) then E.P (s : ℕ) (z s) (x s) (x t) else 1)
          * E.P n (z (Fin.last n)) (x (Fin.last n)) a := by
    rw [Fin.prod_univ_castSucc]
    have hlast : (∏ t : Fin (n + 1 + 1),
        if ((Fin.last (n + 1) : Fin (n + 1 + 1)) : ℕ) + 1 = (t : ℕ) then
          E.P ((Fin.last (n + 1) : Fin (n + 1 + 1)) : ℕ)
            ((Fin.snoc z b : Fin (n + 1 + 1) → Bool) (Fin.last (n + 1)))
            ((Fin.snoc x a : Fin (n + 1 + 1) → S) (Fin.last (n + 1)))
            ((Fin.snoc x a : Fin (n + 1 + 1) → S) t)
        else 1) = 1 := by
      refine Finset.prod_eq_one fun t _ => if_neg ?_
      have := t.isLt
      simp only [Fin.val_last]
      omega
    rw [hlast, mul_one]
    have hs : ∀ s : Fin (n + 1), (∏ t : Fin (n + 1 + 1),
        if ((Fin.castSucc s : Fin (n + 1 + 1)) : ℕ) + 1 = (t : ℕ) then
          E.P ((Fin.castSucc s : Fin (n + 1 + 1)) : ℕ)
            ((Fin.snoc z b : Fin (n + 1 + 1) → Bool) (Fin.castSucc s))
            ((Fin.snoc x a : Fin (n + 1 + 1) → S) (Fin.castSucc s))
            ((Fin.snoc x a : Fin (n + 1 + 1) → S) t)
        else 1)
        = (∏ t : Fin (n + 1), if (s : ℕ) + 1 = (t : ℕ) then E.P (s : ℕ) (z s) (x s) (x t) else 1)
          * (if s = Fin.last n then E.P n (z (Fin.last n)) (x (Fin.last n)) a else 1) := by
      intro s
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
      congr 1
      by_cases h : s = Fin.last n
      · subst h
        simp
      · rw [if_neg h, if_neg]
        intro h'
        exact h (Fin.ext (by simpa using h'))
    rw [Finset.prod_congr rfl (fun s _ => hs s), Finset.prod_mul_distrib]
    simp
  unfold Env.pathWeight
  rw [h1, h2, h3]
  ring

/-- Consistency: summing the weight of horizon `n + 1` over the last state and action gives the
weight of horizon `n`. -/
lemma sum_pathWeight_snoc (E : Env S) (n : ℕ) (q : ℕ → ℝ) (x : Fin n → S) (z : Fin n → Bool) :
    ∑ a : S, ∑ b : Bool, E.pathWeight (n + 1) q (Fin.snoc x a) (Fin.snoc z b)
      = E.pathWeight n q x z := by
  cases n with
  | zero =>
    simp only [pathWeight_one, pathWeight_zero, Fin.snoc_last, ← Finset.mul_sum, sum_bool_ite,
      mul_one]
    exact E.ρ_sum
  | succ n =>
    simp only [pathWeight_snoc, ← Finset.mul_sum, sum_bool_ite, E.P_row_sum, mul_one]

/-- The path weights of any horizon sum to one. -/
lemma sum_pathWeight (E : Env S) (q : ℕ → ℝ) (n : ℕ) :
    ∑ x : Fin n → S, ∑ z : Fin n → Bool, E.pathWeight n q x z = 1 := by
  induction n with
  | zero => simp [pathWeight_zero]
  | succ n ih =>
    rw [sum_snoc₂]
    simp only [sum_pathWeight_snoc]
    exact ih

end TPG_FB_Prob

theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1) :
    IsProbabilityMeasure (E.trajLaw T q) := by
  have hprob : ∀ p : (Fin T → S) × (Fin T → Bool), IsProbabilityMeasure (E.rewardLaw p.1 p.2) :=
    fun p => by unfold Env.rewardLaw; infer_instance
  have h := (integral_trajLaw E T q hq (fun _ => (1 : ℝ)) measurable_const
    (fun p => integrable_const _)).2
  simp only [integral_const, smul_eq_mul, mul_one, probReal_univ] at h
  rw [Fintype.sum_prod_type, TPG_FB_Prob.sum_pathWeight] at h
  exact ⟨(ENNReal.toReal_eq_one_iff _).1 h⟩
