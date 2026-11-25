-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_degLT_succ_growth_natPow_86a645ae5dec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:39.233599+00:00
-- url     : https://prove2.me/submissions/7cfc603a-5e3b-45c7-829b-86cd50840421

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegLTGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegLTGrowth
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_mixedDiff_of_fin_zero_39ff712c69c1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_degLT_diffStep_of_degLT_succ_1dbb35a03f6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_diffStep_single_natCast_044387e002a6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_sum_add_pi_single_one_3a9c5801f689
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_abs_sub_le_of_unit_steps_95b851164d45

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
open GroundTheory.Heights₂.Heights.NumbersDVR
variable {K : Type} [Fintype K] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (n : ℕ) : ∀ g : (K → ℤ) → ℤ, DegLT g (n + 1) →
    ∃ (A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : K → ℕ, (∀ k, A ≤ a k) →
      |(g (fun k => (a k : ℤ)) : ℝ)| ≤ C * (((∑ k, a k : ℕ) : ℝ) + 1) ^ n := by
  induction n with
  | zero =>
    intro g hg
    have hev : ∀ᶠ m in Filter.atTop, ∀ k, diffStep (Pi.single k 1) g m = 0 := by
      refine Filter.eventually_all.2 fun k => ?_
      have := degLT_diffStep_of_degLT_succ hg (Pi.single k 1) Fin.elim0
      simpa [mixedDiff_of_fin_zero] using this
    obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 hev
    set A : ℕ := ∑ k, (m₀ k).toNat
    have hA : ∀ k, m₀ k ≤ (A : ℤ) := by
      intro k
      calc m₀ k ≤ ((m₀ k).toNat : ℤ) := Int.self_le_toNat _
        _ ≤ (A : ℤ) := by
          exact_mod_cast Finset.single_le_sum (f := fun k => (m₀ k).toNat)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    refine ⟨A, |(g (fun _ => (A : ℤ)) : ℝ)|, abs_nonneg _, fun a ha => ?_⟩
    have hw := abs_sub_le_of_unit_steps (fun a : K → ℕ => g (fun k => (a k : ℤ))) A 0 le_rfl (∑ k, a k) a rfl ha
      (fun m k hm _ => by
        have hge : m₀ ≤ fun j => ((m + Pi.single k 1 : K → ℕ) j : ℤ) := by
          intro j
          have := hA j
          have := hm j
          simp only [Pi.add_apply]
          push_cast
          have : (0 : ℤ) ≤ ((Pi.single k 1 : K → ℕ) j : ℤ) := Nat.cast_nonneg _
          omega
        have := hm₀ _ hge k
        rw [diffStep_single_natCast] at this
        rw [sub_eq_zero.mp this]
        simp)
    simp only [zero_mul] at hw
    simp only [pow_zero, mul_one]
    have := abs_sub_abs_le_abs_sub (g (fun k => (a k : ℤ)) : ℝ) (g (fun _ => (A : ℤ)) : ℝ)
    linarith
  | succ n ih =>
    intro g hg
    have hd : ∀ k, ∃ (A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : K → ℕ, (∀ j, A ≤ a j) →
        |(diffStep (Pi.single k 1) g (fun j => (a j : ℤ)) : ℝ)| ≤
          C * (((∑ j, a j : ℕ) : ℝ) + 1) ^ n :=
      fun k => ih _ (degLT_diffStep_of_degLT_succ hg _)
    choose Ak Ck hCk hbk using hd
    set A : ℕ := ∑ k, Ak k
    set C : ℝ := ∑ k, Ck k
    have hC : 0 ≤ C := Finset.sum_nonneg fun k _ => hCk k
    have hAk : ∀ k, Ak k ≤ A := fun k =>
      Finset.single_le_sum (f := Ak) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have hCk' : ∀ k, Ck k ≤ C := fun k =>
      Finset.single_le_sum (f := Ck) (fun k _ => hCk k) (Finset.mem_univ k)
    set G0 : ℝ := |(g (fun _ => (A : ℤ)) : ℝ)|
    refine ⟨A, G0 + C, by positivity, fun a ha => ?_⟩
    set X : ℝ := ((∑ k, a k : ℕ) : ℝ) + 1 with hX
    have hS0 : (0 : ℝ) ≤ ((∑ k, a k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hX1 : 1 ≤ X := by simp only [X]; linarith
    have hw := abs_sub_le_of_unit_steps (fun a : K → ℕ => g (fun k => (a k : ℤ))) A (C * X ^ n) (by positivity)
      (∑ k, a k) a rfl ha (fun m k hm hs => by
        have h1 := hbk k (m + Pi.single k 1) (fun j => le_trans (hAk k)
          (le_trans (hm j) (by simp)))
        rw [diffStep_single_natCast] at h1
        push_cast at h1 ⊢
        refine le_trans h1 ?_
        have hs' : ((∑ j, (m + Pi.single k 1 : K → ℕ) j : ℕ) : ℝ) + 1 ≤ X := by
          rw [sum_add_pi_single_one]; simp only [X]; exact_mod_cast Nat.add_le_add_right hs 1
        have h0 : (0 : ℝ) ≤ ((∑ j, (m + Pi.single k 1 : K → ℕ) j : ℕ) : ℝ) + 1 := by positivity
        push_cast at hs' h0
        exact le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hs' n) (hCk k))
          (mul_le_mul_of_nonneg_right (hCk' k) (by positivity)))
    simp only at hw
    have htri := abs_sub_abs_le_abs_sub (g (fun k => (a k : ℤ)) : ℝ) (g (fun _ => (A : ℤ)) : ℝ)
    have hSX : ((∑ k, a k : ℕ) : ℝ) ≤ X := by simp only [X]; linarith
    have hXn : X ^ n * ((∑ k, a k : ℕ) : ℝ) ≤ X ^ (n + 1) := by
      rw [pow_succ]; exact mul_le_mul_of_nonneg_left hSX (by positivity)
    have hX1n : 1 ≤ X ^ (n + 1) := one_le_pow₀ hX1
    have hG0 : 0 ≤ G0 := abs_nonneg _
    push_cast at hw htri
    calc |(g (fun k => (a k : ℤ)) : ℝ)|
        ≤ G0 + C * X ^ n * ((∑ k, a k : ℕ) : ℝ) := by push_cast; simp only [G0]; linarith
      _ ≤ G0 * X ^ (n + 1) + C * X ^ (n + 1) := by
          have := mul_le_mul_of_nonneg_left hXn hC
          have := mul_le_mul_of_nonneg_left hX1n hG0
          nlinarith
      _ = (G0 + C) * X ^ (n + 1) := by ring
end GroundTheory.Heights₂.Heights.HilbertSamuel
