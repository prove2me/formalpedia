-- Prove2me | solution 1 for SluggishCapability.Myopic.step_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:49:21.497702+00:00
-- url     : https://prove2.me/submissions/25cccb3a-0402-417f-9a25-cea04aeb5507

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_SluggishCapability_Myopic_Setting
import Theorems.Thm_MarkovMixing_exists_unique_stationary
import Theorems.Thm_SluggishCapability_Myopic_ext_marginal_stationary

open MarkovMixing
open SluggishCapability.Myopic

namespace SlugStep3Aux

lemma myopicStep_le (m d : ℕ) : myopicStep m d ≤ max m d := by
  unfold myopicStep; split_ifs <;> omega

lemma sum_fin_ite (M k : ℕ) (hk : k ≤ M) (a : ℝ) (G : ℕ → ℝ) :
    ∑ m : Fin (M + 1), (if (m : ℕ) = k then a else 0) * G m = a * G k := by
  rw [Finset.sum_eq_single (⟨k, by omega⟩ : Fin (M + 1))]
  · simp
  · intro b _ hb
    rw [if_neg, zero_mul]
    intro h; apply hb; ext; exact h
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Expectation of a function of the next state under a stationary law. -/
lemma stat_expect {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (f : S → ℕ) (M : ℕ) (hM : ∀ s, f s ≤ M)
    (ν : Fin (M + 1) × S → ℝ) (hν : IsStationary (extKernel P f M) ν) (G : ℕ → S → ℝ) :
    ∑ y : Fin (M + 1) × S, ν y * G y.1 y.2 =
      ∑ x : Fin (M + 1) × S, ∑ s' : S, ν x * P x.2 s' * G (myopicStep x.1 (f s')) s' := by
  calc ∑ y : Fin (M + 1) × S, ν y * G y.1 y.2
      = ∑ y : Fin (M + 1) × S, (∑ x, ν x * extKernel P f M x y) * G y.1 y.2 := by
        refine Finset.sum_congr rfl fun y _ => ?_
        have := congrFun hν.2 y
        simp only [Matrix.vecMul, dotProduct] at this
        rw [this]
    _ = ∑ x, ν x * ∑ y : Fin (M + 1) × S, extKernel P f M x y * G y.1 y.2 := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    _ = _ := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s' _ => ?_
        simp only [extKernel]
        have hk : myopicStep (x.1 : ℕ) (f s') ≤ M :=
          (myopicStep_le _ _).trans (max_le (Nat.lt_succ_iff.mp x.1.2) (hM s'))
        rw [sum_fin_ite M _ hk (P x.2 s') (fun m => G m s')]
        ring

lemma key (μ : ℕ) (hμ : 1 ≤ μ) (m d : ℕ) (hm : 2 * μ ≤ m) :
    ((μ : ℝ) + 1 / 2) * (1 + (myopicStep m d : ℝ) - m) ≤ d := by
  unfold myopicStep
  have hμr : (1 : ℝ) ≤ μ := by exact_mod_cast hμ
  have hmr : (2 * μ : ℝ) ≤ m := by exact_mod_cast hm
  split_ifs with h1 h2
  · have : (m : ℝ) + 1 ≤ d := by exact_mod_cast h1
    push_cast; nlinarith
  · subst h2; nlinarith
  · have h3 : 1 ≤ m := by omega
    rw [Nat.cast_sub h3]; push_cast
    have : (0 : ℝ) ≤ d := by positivity
    nlinarith

end SlugStep3Aux

open SlugStep3Aux

theorem solution (μ : ℕ) (hμ : 1 ≤ μ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hεhalf : ε < 1 / 2)
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (f : S → ℕ) (hfeas : IsFeasibleProgram P f μ ε)
    (M : ℕ) (hM : ∀ s, f s ≤ M)
    (ν : Fin (M + 1) × S → ℝ) (hν : IsStationary (extKernel P f M) ν) :
    ∃ x : Fin (M + 1) × S, 0 < ν x ∧ (x.1 : ℕ) ≤ 2 * μ - 1 := by
  obtain ⟨hPst, hirr, lam, hlam, hcon⟩ := hfeas
  by_contra hcontra
  push_neg at hcontra
  have hsupp : ∀ x : Fin (M + 1) × S, 0 < ν x → 2 * μ ≤ (x.1 : ℕ) := by
    intro x hx; have := hcontra x hx; omega
  -- the state marginal is `lam`
  have hmarg := (ext_marginal_stationary P f M hPst hM).2 ν hν
  obtain ⟨x0, -, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show ∑ x, ν x ≠ 0 by rw [hν.1.2]; norm_num)
  haveI : Nonempty S := ⟨x0.2⟩
  obtain ⟨π, -, huniq⟩ := exists_unique_stationary P hPst hirr
  have hml : (fun s => ∑ m : Fin (M + 1), ν (m, s)) = lam :=
    (huniq _ hmarg).trans (huniq _ hlam).symm
  -- expected challenge
  have hEd : ∑ y : Fin (M + 1) × S, ν y * (f y.2 : ℝ) ≤ μ + ε := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc ∑ s, ∑ m : Fin (M + 1), ν (m, s) * (f s : ℝ)
        = ∑ s, (∑ m : Fin (M + 1), ν (m, s)) * (f s : ℝ) := by simp_rw [Finset.sum_mul]
      _ = ∑ s, lam s * (f s : ℝ) := by rw [← hml]
      _ ≤ _ := hcon
  have e1 := stat_expect P f M hM ν hν (fun _ s => (f s : ℝ))
  have e2 := stat_expect P f M hM ν hν (fun m _ => (m : ℝ))

  -- row sums
  have hrow : ∀ x : Fin (M + 1) × S, ∑ s', P x.2 s' = 1 := fun x => hPst.2 x.2
  have e3 : ∑ y : Fin (M + 1) × S, ν y * ((y.1 : ℕ) : ℝ) =
      ∑ x : Fin (M + 1) × S, ∑ s' : S, ν x * P x.2 s' * ((x.1 : ℕ) : ℝ) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, hrow, mul_one]
  have e4 : ∑ x : Fin (M + 1) × S, ∑ s' : S, ν x * P x.2 s' = 1 := by
    rw [← hν.1.2]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum, hrow, mul_one]
  have hpt : ∀ x : Fin (M + 1) × S, ∀ s' : S,
      ν x * P x.2 s' * (((μ : ℝ) + 1 / 2) * (1 + (myopicStep x.1 (f s') : ℝ) - (x.1 : ℕ)))
        ≤ ν x * P x.2 s' * (f s' : ℝ) := by
    intro x s'
    rcases (hν.1.1 x).lt_or_eq with hx | hx
    · exact mul_le_mul_of_nonneg_left (key μ hμ _ _ (hsupp x hx))
        (mul_nonneg hx.le (hPst.1 _ _))
    · rw [← hx]; simp
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) =>
    Finset.sum_le_sum fun s' (_ : s' ∈ Finset.univ) => hpt x s'
  have hL : ∑ x : Fin (M + 1) × S, ∑ s' : S,
      ν x * P x.2 s' * (((μ : ℝ) + 1 / 2) * (1 + (myopicStep x.1 (f s') : ℝ) - (x.1 : ℕ)))
      = ((μ : ℝ) + 1 / 2) * (∑ x : Fin (M + 1) × S, ∑ s' : S, ν x * P x.2 s'
          + ∑ x : Fin (M + 1) × S, ∑ s' : S, ν x * P x.2 s' * (myopicStep x.1 (f s') : ℝ)
          - ∑ x : Fin (M + 1) × S, ∑ s' : S, ν x * P x.2 s' * ((x.1 : ℕ) : ℝ)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => by ring
  rw [hL, e4, ← e2, ← e3, ← e1] at hsum
  linarith
