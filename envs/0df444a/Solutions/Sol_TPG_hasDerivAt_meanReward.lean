-- Prove2me | solution 1 for TPG.hasDerivAt_meanReward
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:25:33.596981+00:00
-- url     : https://prove2.me/submissions/f37e8fe7-0b0d-4bcd-a6ef-dfe91777c0bf

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Markov
import Definitions.Def_TPG_Bridge

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

namespace TPG_B2_D

variable {S : Type} [Fintype S]

/-- Product rule for a row vector times a matrix, both depending on a real parameter. -/
lemma hasDerivAt_vecMul {v : ℝ → S → ℝ} {v' : S → ℝ} {M : ℝ → Matrix S S ℝ}
    {M' : Matrix S S ℝ} {x : ℝ} (hv : HasDerivAt v v' x)
    (hM : ∀ i j, HasDerivAt (fun θ => M θ i j) (M' i j) x) :
    HasDerivAt (fun θ => Matrix.vecMul (v θ) (M θ))
      (Matrix.vecMul v' (M x) + Matrix.vecMul (v x) M') x := by
  rw [hasDerivAt_pi] at hv ⊢
  intro j
  have h : HasDerivAt (fun θ => ∑ i, v θ i * M θ i j)
      (∑ i, (v' i * M x i j + v x i * M' i j)) x :=
    HasDerivAt.fun_sum (fun i _ => (hv i).mul (hM i j))
  have e : (Matrix.vecMul v' (M x) + Matrix.vecMul (v x) M') j
      = ∑ i, (v' i * M x i j + v x i * M' i j) := by
    rw [Finset.sum_add_distrib]
    rfl
  rw [e]
  exact h

/-- Product rule for the dot product of two vectors depending on a real parameter. -/
lemma hasDerivAt_dotProduct {v w : ℝ → S → ℝ} {v' w' : S → ℝ} {x : ℝ}
    (hv : HasDerivAt v v' x) (hw : HasDerivAt w w' x) :
    HasDerivAt (fun θ => dotProduct (v θ) (w θ))
      (dotProduct v' (w x) + dotProduct (v x) w') x := by
  rw [hasDerivAt_pi] at hv hw
  have h : HasDerivAt (fun θ => ∑ i, v θ i * w θ i)
      (∑ i, (v' i * w x i + v x i * w' i)) x :=
    HasDerivAt.fun_sum (fun i _ => (hv i).mul (hw i))
  have e : dotProduct v' (w x) + dotProduct (v x) w'
      = ∑ i, (v' i * w x i + v x i * w' i) := by
    rw [Finset.sum_add_distrib]
    rfl
  rw [e]
  exact h

/-- Derivative of an affine interpolation between two numbers. -/
lemma hasDerivAt_affine (a b x : ℝ) :
    HasDerivAt (fun θ : ℝ => θ * a + (1 - θ) * b) (a - b) x := by
  have h : HasDerivAt (fun θ : ℝ => θ * (a - b) + b) (a - b) x :=
    (hasDerivAt_mul_const (a - b)).add_const b
  have e : (fun θ : ℝ => θ * a + (1 - θ) * b) = fun θ : ℝ => θ * (a - b) + b := by
    funext θ
    ring
  rw [e]
  exact h

/-- Entrywise derivative of the mixed kernel at a time whose probability is either the
parameter or a constant. -/
lemma hasDerivAt_PMix (E : Env S) (A : ℕ → Prop) [DecidablePred A] (c : ℕ → ℝ) (θ₀ : ℝ)
    (n : ℕ) (i j : S) :
    HasDerivAt (fun θ : ℝ => E.PMix (if A n then θ else c n) n i j)
      ((if A n then E.P n true - E.P n false else (0 : Matrix S S ℝ)) i j) θ₀ := by
  by_cases hA : A n
  · simp only [if_pos hA]
    exact hasDerivAt_affine (E.P n true i j) (E.P n false i j) θ₀
  · simp only [if_neg hA, Matrix.zero_apply]
    exact hasDerivAt_const _ _

/-- Derivative of the mixed reward vector at a time whose probability is either the parameter
or a constant. -/
lemma hasDerivAt_rMix (E : Env S) (A : ℕ → Prop) [DecidablePred A] (c : ℕ → ℝ) (θ₀ : ℝ)
    (n : ℕ) :
    HasDerivAt (fun θ : ℝ => E.rMix (if A n then θ else c n))
      (if A n then (fun x => E.r true x - E.r false x) else (0 : S → ℝ)) θ₀ := by
  rw [hasDerivAt_pi]
  intro x
  by_cases hA : A n
  · simp only [if_pos hA]
    exact hasDerivAt_affine (E.r true x) (E.r false x) θ₀
  · simp only [if_neg hA, Pi.zero_apply]
    exact hasDerivAt_const _ _

variable [DecidableEq S]

lemma stateVec_zero (E : Env S) (q : ℕ → ℝ) : E.stateVec q 0 = E.ρ := by
  simp [Env.stateVec]

lemma stateVec_succ (E : Env S) (q : ℕ → ℝ) (n : ℕ) :
    E.stateVec q (n + 1) = Matrix.vecMul (E.stateVec q n) (E.PMix (q n) n) := by
  simp [Env.stateVec, List.range_succ, Matrix.vecMul_vecMul]

/-- The state distribution at time `t` only depends on the treatment probabilities before `t`. -/
lemma stateVec_congr (E : Env S) (q q' : ℕ → ℝ) (t : ℕ) (h : ∀ s, s < t → q s = q' s) :
    E.stateVec q t = E.stateVec q' t := by
  induction t with
  | zero => rw [stateVec_zero, stateVec_zero]
  | succ n ih =>
    rw [stateVec_succ, stateVec_succ, ih (fun s hs => h s (Nat.lt_succ_of_lt hs)),
      h n (Nat.lt_succ_self n)]

lemma stateVec_update_of_le (E : Env S) (q : ℕ → ℝ) (t u : ℕ) (b : ℝ) (h : t ≤ u) :
    E.stateVec (Function.update q u b) t = E.stateVec q t :=
  stateVec_congr E _ _ t fun s hs => Function.update_of_ne (by omega) _ _

/-- Derivative of the state distribution with respect to the common treatment probability of
the times in `A`. -/
lemma hasDerivAt_stateVec (E : Env S) (A : ℕ → Prop) [DecidablePred A] (c : ℕ → ℝ) (θ₀ : ℝ)
    (t : ℕ) :
    HasDerivAt (fun θ : ℝ => E.stateVec (fun s => if A s then θ else c s) t)
      (∑ u ∈ Finset.range t,
        if A u then
          (E.stateVec (Function.update (fun s => if A s then θ₀ else c s) u 1) t
            - E.stateVec (Function.update (fun s => if A s then θ₀ else c s) u 0) t)
        else 0) θ₀ := by
  induction t with
  | zero =>
    simp only [stateVec_zero, Finset.range_zero, Finset.sum_empty]
    exact hasDerivAt_const _ _
  | succ n ih =>
    simp only [stateVec_succ]
    have h := hasDerivAt_vecMul ih (hasDerivAt_PMix E A c θ₀ n)
    convert h using 1
    rw [Finset.sum_range_succ]
    congr 1
    · rw [Matrix.sum_vecMul]
      refine Finset.sum_congr rfl fun u hu => ?_
      have hu' : u < n := Finset.mem_range.1 hu
      have hne : n ≠ u := by omega
      by_cases hA : A u
      · simp only [if_pos hA]
        rw [Matrix.sub_vecMul, Function.update_of_ne hne, Function.update_of_ne hne]
      · simp only [if_neg hA]
        rw [Matrix.zero_vecMul]
    · by_cases hA : A n
      · simp only [if_pos hA]
        rw [stateVec_update_of_le E _ n n 1 le_rfl, stateVec_update_of_le E _ n n 0 le_rfl,
          Function.update_self, Function.update_self, ← Matrix.vecMul_sub]
        congr 1
        ext i j
        simp [Env.PMix]
      · simp only [if_neg hA]
        rw [Matrix.vecMul_zero]

end TPG_B2_D

theorem solution {S : Type} [Fintype S] [DecidableEq S]
    (E : Env S) (t : ℕ) (A : ℕ → Prop) [DecidablePred A] (c : ℕ → ℝ) (θ₀ : ℝ) :
    HasDerivAt (fun θ : ℝ => E.meanReward (fun s => if A s then θ else c s) t)
      (∑ u ∈ Finset.range (t + 1),
        if A u then
          (E.meanReward (Function.update (fun s => if A s then θ₀ else c s) u 1) t
            - E.meanReward (Function.update (fun s => if A s then θ₀ else c s) u 0) t)
        else 0)
      θ₀ := by
  have h := TPG_B2_D.hasDerivAt_dotProduct (TPG_B2_D.hasDerivAt_stateVec E A c θ₀ t)
    (TPG_B2_D.hasDerivAt_rMix E A c θ₀ t)
  simp only [Env.meanReward]
  convert h using 1
  rw [Finset.sum_range_succ, sum_dotProduct]
  congr 1
  · refine Finset.sum_congr rfl fun u hu => ?_
    have hu' : u < t := Finset.mem_range.1 hu
    have hne : t ≠ u := by omega
    by_cases hA : A u
    · simp only [if_pos hA]
      rw [sub_dotProduct, Function.update_of_ne hne, Function.update_of_ne hne]
    · simp only [if_neg hA]
      rw [zero_dotProduct]
  · by_cases hA : A t
    · simp only [if_pos hA]
      rw [TPG_B2_D.stateVec_update_of_le E _ t t 1 le_rfl,
        TPG_B2_D.stateVec_update_of_le E _ t t 0 le_rfl,
        Function.update_self, Function.update_self, ← dotProduct_sub]
      congr 1
      ext x
      simp [Env.rMix]
    · simp only [if_neg hA]
      rw [dotProduct_zero]
