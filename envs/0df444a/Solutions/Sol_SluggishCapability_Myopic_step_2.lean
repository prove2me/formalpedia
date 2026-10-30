-- Prove2me | solution 1 for SluggishCapability.Myopic.step_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:53:50.716638+00:00
-- url     : https://prove2.me/submissions/eba60cbf-da28-4a35-a515-3e76d234c1e7

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_SluggishCapability_Myopic_Setting
import Theorems.Thm_MarkovMixing_exists_unique_stationary
import Theorems.Thm_SluggishCapability_Myopic_ext_marginal_stationary
import Theorems.Thm_SluggishCapability_Myopic_step_1_eq_4

open MarkovMixing
open SluggishCapability.Myopic

namespace SlugStep2Aux

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

end SlugStep2Aux

open SlugStep2Aux

theorem solution (μ : ℕ) (hμ : 1 ≤ μ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (f : S → ℕ) (hfeas : IsFeasibleProgram P f μ ε)
    (M : ℕ) (hM : ∀ s, f s ≤ M)
    (ν : Fin (M + 1) × S → ℝ) (hν : IsStationary (extKernel P f M) ν) :
    ∑ x : Fin (M + 1) × S, ν x * (x.1 : ℝ) ≤
      2 * ((μ : ℝ) + ε) - ∑ x : Fin (M + 1) × S, ∑ s' : S,
        (if f s' = (x.1 : ℕ) then ν x * P x.2 s' * (x.1 : ℝ) else 0) := by
  obtain ⟨hPst, hirr, lam, hlam, hcon⟩ := hfeas
  have h4 := step_1_eq_4 P f M hPst hM ν hν
  have hmarg := (ext_marginal_stationary P f M hPst hM).2 ν hν
  obtain ⟨x0, -, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show ∑ x, ν x ≠ 0 by rw [hν.1.2]; norm_num)
  haveI : Nonempty S := ⟨x0.2⟩
  obtain ⟨π, -, huniq⟩ := exists_unique_stationary P hPst hirr
  have hml : (fun s => ∑ m : Fin (M + 1), ν (m, s)) = lam :=
    (huniq _ hmarg).trans (huniq _ hlam).symm
  have hEd : ∑ y : Fin (M + 1) × S, ν y * (f y.2 : ℝ) ≤ μ + ε := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc ∑ s, ∑ m : Fin (M + 1), ν (m, s) * (f s : ℝ)
        = ∑ s, (∑ m : Fin (M + 1), ν (m, s)) * (f s : ℝ) := by simp_rw [Finset.sum_mul]
      _ = ∑ s, lam s * (f s : ℝ) := by rw [← hml]
      _ ≤ _ := hcon
  have e1 := stat_expect P f M hM ν hν (fun _ s => (f s : ℝ))
  have hrow : ∀ x : Fin (M + 1) × S, ∑ s', P x.2 s' = 1 := fun x => hPst.2 x.2
  have e3 : ∑ y : Fin (M + 1) × S, ν y * ((y.1 : ℕ) : ℝ) =
      ∑ x : Fin (M + 1) × S, ∑ s' : S, ν x * P x.2 s' * ((x.1 : ℕ) : ℝ) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, hrow, mul_one]
  have hpt : ∀ x : Fin (M + 1) × S, ∀ s' : S,
      ν x * P x.2 s' * ((x.1 : ℕ) : ℝ) ≤
        2 * (ν x * P x.2 s' * (f s' : ℝ))
        - (if f s' = (x.1 : ℕ) then ν x * P x.2 s' * (x.1 : ℝ) else 0)
        + (if f s' < (x.1 : ℕ) then ν x * P x.2 s' * (x.1 : ℝ) else 0)
        - (if (x.1 : ℕ) < f s' then ν x * P x.2 s' * ((x.1 : ℝ) + 1) else 0) := by
    intro x s'
    have hw : 0 ≤ ν x * P x.2 s' := mul_nonneg (hν.1.1 x) (hPst.1 _ _)
    set w := ν x * P x.2 s'
    have hd : (0 : ℝ) ≤ f s' := by positivity
    rcases lt_trichotomy (x.1 : ℕ) (f s') with h | h | h
    · rw [if_neg (by omega), if_neg (by omega), if_pos h]
      have : ((x.1 : ℕ) : ℝ) + 1 ≤ f s' := by exact_mod_cast h
      nlinarith
    · rw [if_pos h.symm, if_neg (by omega), if_neg (by omega)]
      have : ((x.1 : ℕ) : ℝ) = f s' := by exact_mod_cast h
      rw [this]; nlinarith
    · rw [if_neg (by omega), if_pos h, if_neg (by omega)]
      nlinarith
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) =>
    Finset.sum_le_sum fun s' (_ : s' ∈ Finset.univ) => hpt x s'
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [← e3, ← e1, h4] at hsum
  linarith
