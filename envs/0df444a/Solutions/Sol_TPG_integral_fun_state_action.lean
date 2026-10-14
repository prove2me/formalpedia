-- Prove2me | solution 1 for TPG.integral_fun_state_action
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:15:47.405496+00:00
-- url     : https://prove2.me/submissions/7742b253-75e0-4e10-913a-707ee144428c

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Markov
import Theorems.Thm_TPG_integral_trajLaw

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

namespace TPG_FB_G

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

lemma sum_pathWeight_mul_init (E : Env S) (n : ℕ) (q : ℕ → ℝ)
    (G : (Fin n → S) → (Fin n → Bool) → ℝ) :
    ∑ x : Fin (n + 1) → S, ∑ z : Fin (n + 1) → Bool,
        E.pathWeight (n + 1) q x z * G (Fin.init x) (Fin.init z)
      = ∑ x : Fin n → S, ∑ z : Fin n → Bool, E.pathWeight n q x z * G x z := by
  rw [sum_snoc₂]
  simp only [Fin.init_snoc, ← Finset.sum_mul, sum_pathWeight_snoc]

/-- A function of the first `m` steps has the same weighted sum under every horizon `n ≥ m`. -/
lemma sum_pathWeight_mul_castLE (E : Env S) (q : ℕ → ℝ) (m : ℕ)
    (G : (Fin m → S) → (Fin m → Bool) → ℝ) (n : ℕ) (h : m ≤ n) :
    ∑ x : Fin n → S, ∑ z : Fin n → Bool,
        E.pathWeight n q x z * G (fun i => x (Fin.castLE h i)) (fun i => z (Fin.castLE h i))
      = ∑ x : Fin m → S, ∑ z : Fin m → Bool, E.pathWeight m q x z * G x z := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ n h ih =>
    rw [← ih]
    exact sum_pathWeight_mul_init E n q
      (fun x z => G (fun i => x (Fin.castLE h i)) (fun i => z (Fin.castLE h i)))

lemma stateVec_zero [DecidableEq S] (E : Env S) (q : ℕ → ℝ) : E.stateVec q 0 = E.ρ := by
  simp [Env.stateVec]

lemma stateVec_succ [DecidableEq S] (E : Env S) (q : ℕ → ℝ) (n : ℕ) :
    E.stateVec q (n + 1) = Matrix.vecMul (E.stateVec q n) (E.PMix (q n) n) := by
  simp [Env.stateVec, List.range_succ, Matrix.vecMul_vecMul]

/-- Marginal of the state and action at the last time of horizon `n + 1`. -/
lemma sum_pathWeight_last [DecidableEq S] (E : Env S) (q : ℕ → ℝ) (n : ℕ) :
    ∀ g : S → Bool → ℝ,
    ∑ x : Fin (n + 1) → S, ∑ z : Fin (n + 1) → Bool,
        E.pathWeight (n + 1) q x z * g (x (Fin.last n)) (z (Fin.last n))
      = ∑ a : S, E.stateVec q n a * (q n * g a true + (1 - q n) * g a false) := by
  induction n with
  | zero =>
    intro g
    rw [sum_snoc₂]
    simp only [pathWeight_one, Fin.snoc_last, stateVec_zero, Fintype.sum_unique, Fintype.sum_bool,
      if_true, Bool.false_eq_true, if_false]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  | succ n ih =>
    intro g
    rw [sum_snoc₂]
    simp only [pathWeight_snoc, Fin.snoc_last]
    have hstep : ∀ (x : Fin (n + 1) → S) (z : Fin (n + 1) → Bool),
        ∑ a : S, ∑ b : Bool, E.pathWeight (n + 1) q x z * E.P n (z (Fin.last n)) (x (Fin.last n)) a
            * (if b then q (n + 1) else 1 - q (n + 1)) * g a b
          = E.pathWeight (n + 1) q x z *
              (fun a' b' => ∑ a : S, E.P n b' a' a
                * (q (n + 1) * g a true + (1 - q (n + 1)) * g a false))
              (x (Fin.last n)) (z (Fin.last n)) := by
      intro x z
      simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    have key := ih (fun a' b' => ∑ a : S, E.P n b' a' a
      * (q (n + 1) * g a true + (1 - q (n + 1)) * g a false))
    beta_reduce at key
    simp only [hstep]
    rw [key, stateVec_succ]
    simp only [Matrix.vecMul, dotProduct, Env.PMix, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

/-- **Marginalization of the path weights**: the joint weight of the state and action at one
time `t` of a horizon-`T` path is `stateVec q t` times the Bernoulli(`q t`) action weight. -/
lemma sum_pathWeight_marginal [DecidableEq S] (E : Env S) (T : ℕ) (q : ℕ → ℝ) (t : Fin T)
    (g : S → Bool → ℝ) :
    ∑ x : Fin T → S, ∑ z : Fin T → Bool, E.pathWeight T q x z * g (x t) (z t)
      = ∑ a : S, E.stateVec q (t : ℕ) a
          * (q (t : ℕ) * g a true + (1 - q (t : ℕ)) * g a false) := by
  have h : (t : ℕ) + 1 ≤ T := t.isLt
  rw [← sum_pathWeight_last E q (t : ℕ) g,
    ← sum_pathWeight_mul_castLE E q ((t : ℕ) + 1)
      (fun x z => g (x (Fin.last (t : ℕ))) (z (Fin.last (t : ℕ)))) T h]
  have ht : Fin.castLE h (Fin.last (t : ℕ)) = t := Fin.ext rfl
  simp only [ht]

end TPG_FB_G

theorem solution {S : Type} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (t : Fin T) (g : S → Bool → ℝ) :
    ∫ ω, g (X t ω) (Z t ω) ∂(E.trajLaw T q)
      = ∑ a : S, E.stateVec q (t : ℕ) a
          * (q (t : ℕ) * g a true + (1 - q (t : ℕ)) * g a false) := by
  have hprob : ∀ p : (Fin T → S) × (Fin T → Bool), IsProbabilityMeasure (E.rewardLaw p.1 p.2) :=
    fun p => by unfold Env.rewardLaw; infer_instance
  have hXZ : Measurable (fun ω : Traj S T => (X t ω, Z t ω)) := by
    show Measurable (fun ω : Traj S T => ((ω t).1, (ω t).2.1))
    exact (measurable_fst.comp (measurable_pi_apply t)).prodMk
      (measurable_fst.comp (measurable_snd.comp (measurable_pi_apply t)))
  have hF : Measurable (fun ω : Traj S T => g (X t ω) (Z t ω)) :=
    (measurable_of_finite (fun p : S × Bool => g p.1 p.2)).comp hXZ
  have hval : ∀ (p : (Fin T → S) × (Fin T → Bool)) (y : Fin T → ℝ),
      g (X t (embedPath p.1 p.2 y)) (Z t (embedPath p.1 p.2 y)) = g (p.1 t) (p.2 t) :=
    fun p y => rfl
  have hint : ∀ p : (Fin T → S) × (Fin T → Bool),
      Integrable (fun y : Fin T → ℝ =>
        (fun ω : Traj S T => g (X t ω) (Z t ω)) (embedPath p.1 p.2 y)) (E.rewardLaw p.1 p.2) := by
    intro p
    simp only [hval]
    exact integrable_const _
  rw [(integral_trajLaw E T q hq _ hF hint).2]
  simp only [hval, integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [Fintype.sum_prod_type]
  exact TPG_FB_G.sum_pathWeight_marginal E T q t g
