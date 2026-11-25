-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_walk_bound_53e030d539c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:48.972315+00:00
-- url     : https://prove2.me/submissions/80bc0b74-a198-4d30-99f8-a9b72959309b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K : Type*} [Fintype K] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (g : (K → ℕ) → ℝ) (a₀ : ℕ) (B : ℝ) (hB : 0 ≤ B) (n : ℕ)
    (hstep : ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) → ∀ b, a₀ < a b →
      |g a - g (Function.update a b (a b - 1))| ≤ B * ((∑ k, (a k : ℝ)) + 1) ^ n) :
    ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |g a| ≤ |g (fun _ => a₀)| + B * ((∑ k, (a k : ℝ)) + 1) ^ (n + 1) := by
  suffices H : ∀ N : ℕ, ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) → ∑ k, (a k - a₀) = N →
      |g a| ≤ |g (fun _ => a₀)| + B * ((∑ k, (a k : ℝ)) + 1) ^ (n + 1) from
    fun a ha => H _ a ha rfl
  intro N
  induction N with
  | zero =>
    intro a ha hN
    have hEq : a = fun _ => a₀ := by
      funext k
      have := (Finset.sum_eq_zero_iff.mp hN) k (Finset.mem_univ k)
      have := ha k
      omega
    subst hEq
    have : 0 ≤ B * ((∑ _k : K, (a₀ : ℝ)) + 1) ^ (n + 1) := by positivity
    linarith
  | succ N ih =>
    intro a ha hN
    obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hN.trans_ne (Nat.succ_ne_zero N))
    have hab : a₀ < a b := by omega
    set a' := Function.update a b (a b - 1) with ha'
    have ha'k : ∀ k, a₀ ≤ a' k := by
      intro k
      by_cases hk : k = b
      · subst hk; simp [a']; omega
      · simp [a', hk, ha k]
    have hsplit : ∀ c : K → ℕ, ∑ k, (c k - a₀) = (c b - a₀) + ∑ k ∈ Finset.univ.erase b, (c k - a₀) :=
      fun c => (Finset.add_sum_erase _ _ (Finset.mem_univ b)).symm
    have hsplitR : ∀ c : K → ℕ, ∑ k, (c k : ℝ) = (c b : ℝ) + ∑ k ∈ Finset.univ.erase b, (c k : ℝ) :=
      fun c => (Finset.add_sum_erase _ _ (Finset.mem_univ b)).symm
    have hrest : ∀ k ∈ Finset.univ.erase b, a' k = a k := by
      intro k hk
      simp [a', Finset.ne_of_mem_erase hk]
    have hN' : ∑ k, (a' k - a₀) = N := by
      rw [hsplit a', Finset.sum_congr rfl (fun k hk => by rw [hrest k hk])]
      rw [hsplit a] at hN
      simp only [a', Function.update_self]
      omega
    have hs : ∑ k, (a' k : ℝ) + 1 = ∑ k, (a k : ℝ) := by
      rw [hsplitR a', hsplitR a, Finset.sum_congr rfl (fun k hk => by rw [hrest k hk])]
      simp only [a', Function.update_self]
      rw [Nat.cast_sub (by omega : 1 ≤ a b)]
      push_cast
      ring
    have h1 := ih a' ha'k hN'
    have h2 := hstep a ha b hab
    rw [hs] at h1
    set s := ∑ k, (a k : ℝ)
    have hs0 : 0 ≤ s := Finset.sum_nonneg (fun k _ => Nat.cast_nonneg _)
    have hpow : s ^ (n + 1) + (s + 1) ^ n ≤ (s + 1) ^ (n + 1) := by
      have : s ^ n ≤ (s + 1) ^ n := pow_le_pow_left₀ hs0 (by linarith) n
      rw [pow_succ, pow_succ]
      nlinarith [pow_nonneg hs0 n]
    have habs : |g a| ≤ |g a'| + |g a - g a'| := by
      have := abs_sub_abs_le_abs_sub (g a) (g a')
      linarith
    calc |g a| ≤ |g a'| + |g a - g a'| := habs
      _ ≤ (|g (fun _ => a₀)| + B * s ^ (n + 1)) + B * (s + 1) ^ n := add_le_add h1 h2
      _ = |g (fun _ => a₀)| + B * (s ^ (n + 1) + (s + 1) ^ n) := by ring
      _ ≤ |g (fun _ => a₀)| + B * (s + 1) ^ (n + 1) := by
        gcongr
end GroundTheory.Heights₂.Heights.HilbertSamuel
