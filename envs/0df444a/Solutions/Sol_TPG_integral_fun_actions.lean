-- Prove2me | solution 1 for TPG.integral_fun_actions
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:32:11.404042+00:00
-- url     : https://prove2.me/submissions/81400728-6c75-4bb2-8402-1e1c6cdeaf69

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Markov
import Theorems.Thm_TPG_integral_trajLaw

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

namespace TPG_VA_A

/-- A sum over tuples of length `n + 1` splits into a sum over the first `n` entries and the
last entry. -/
lemma sum_snoc {α : Type} [Fintype α] {M : Type} [AddCommMonoid M] (n : ℕ)
    (f : (Fin (n + 1) → α) → M) :
    ∑ x, f x = ∑ x : Fin n → α, ∑ a : α, f (Fin.snoc x a) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => α)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

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

/-- **Marginal of the action path.** Summing the path weight over all state paths leaves the
product of the Bernoulli weights of the actions. -/
lemma sum_pathWeight_states (E : Env S) (q : ℕ → ℝ) (n : ℕ) :
    ∀ z : Fin n → Bool,
      ∑ x : Fin n → S, E.pathWeight n q x z
        = ∏ t : Fin n, if z t then q (t : ℕ) else 1 - q (t : ℕ) := by
  induction n with
  | zero =>
    intro z
    simp [pathWeight_zero]
  | succ n ih =>
    intro z
    obtain ⟨z', b, rfl⟩ : ∃ (z' : Fin n → Bool) (b : Bool), z = Fin.snoc z' b :=
      ⟨Fin.init z, z (Fin.last n), (Fin.snoc_init_self z).symm⟩
    rw [sum_snoc, Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
    rw [← ih z']
    cases n with
    | zero =>
      simp only [pathWeight_one, pathWeight_zero, Fin.snoc_last, ← Finset.sum_mul, E.ρ_sum,
        Fintype.sum_unique, one_mul]
    | succ n =>
      simp only [pathWeight_snoc, ← Finset.mul_sum, ← Finset.sum_mul, E.P_row_sum, mul_one]

end TPG_VA_A

theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (g : (Fin T → Bool) → ℝ) :
    ∫ ω, g (fun t => Z t ω) ∂(E.trajLaw T q)
      = ∑ z : Fin T → Bool, (∏ t : Fin T, if z t then q (t : ℕ) else 1 - q (t : ℕ)) * g z := by
  have hprob : ∀ p : (Fin T → S) × (Fin T → Bool), IsProbabilityMeasure (E.rewardLaw p.1 p.2) :=
    fun p => by unfold Env.rewardLaw; infer_instance
  have hZ : Measurable (fun ω : Traj S T => (fun t => Z t ω : Fin T → Bool)) := by
    refine measurable_pi_lambda _ fun t => ?_
    unfold Z
    exact (measurable_pi_apply t).snd.fst
  have hF : Measurable (fun ω : Traj S T => g (fun t => Z t ω)) :=
    (measurable_of_finite g).comp hZ
  have hval : ∀ (p : (Fin T → S) × (Fin T → Bool)) (y : Fin T → ℝ),
      g (fun t => Z t (embedPath p.1 p.2 y)) = g p.2 :=
    fun p y => rfl
  have hint : ∀ p : (Fin T → S) × (Fin T → Bool),
      Integrable (fun y : Fin T → ℝ =>
        (fun ω : Traj S T => g (fun t => Z t ω)) (embedPath p.1 p.2 y)) (E.rewardLaw p.1 p.2) := by
    intro p
    simp only [hval]
    exact integrable_const _
  rw [(integral_trajLaw E T q hq _ hF hint).2]
  simp only [hval, integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [Fintype.sum_prod_type]
  refine Eq.trans Finset.sum_comm ?_
  refine Finset.sum_congr rfl fun z _ => ?_
  show ∑ x : Fin T → S, E.pathWeight T q x z * g z = _
  rw [← Finset.sum_mul, TPG_VA_A.sum_pathWeight_states]
