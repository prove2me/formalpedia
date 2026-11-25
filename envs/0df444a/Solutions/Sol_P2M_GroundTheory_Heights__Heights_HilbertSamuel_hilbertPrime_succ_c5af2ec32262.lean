-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_hilbertPrime_succ_c5af2ec32262
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:06.387927+00:00
-- url     : https://prove2.me/submissions/4ea0fd19-2272-49f0-8433-30fcc9c105ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_walk_bound_53e030d539c4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ofPositionAdditive_apply_bf8ee1efc0e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_multilinear_step_8d3b99047953
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_multilinear_step_le_873981ad91dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_int_eq_of_abs_sub_le_5e7b740318e7

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
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (d : ℕ) (hM : MixedNumberPolynomial.Statement.{u})
    (hI : HilbertIncrement.Statement.{u}) (hmod : HilbertModule.AtDim.{u, u} d) :
    HilbertPrime.AtDim.{u} (d + 1) := by
  intro F _ K _ _ ι _ q hq hdim
  obtain ⟨hsym, hadd⟩ := hM F K ι q (d + 1) hq hdim
  obtain ⟨M, hM0, hE⟩ := multilinear_step_le (ofPositionAdditive (intNum F q) hadd) hsym
  simp only [ofPositionAdditive_apply] at hE
  choose A C hAC using hI d hmod F K ι q hq hdim
  set Cs : ℝ := ∑ b, |C b| with hCs
  set a₀ : ℕ := ∑ b, A b + ⌈Cs⌉₊ with ha₀
  set g : (K → ℕ) → ℝ := fun a => (hilbFn q (fun k => (a k : ℤ)) : ℝ) -
    (intNum F q (fun _ : Fin (d + 1) => fun k => (a k : ℤ)) : ℝ) / ((d + 1).factorial : ℝ) with hg
  have hAb : ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) → ∀ b, ∀ k, A b ≤ a k := by
    intro a ha b k
    refine le_trans ?_ (ha k)
    exact le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le (A j)) (Finset.mem_univ b))
      (Nat.le_add_right _ _)
  have hCb : ∀ b, |C b| ≤ (a₀ : ℝ) := by
    intro b
    calc |C b| ≤ Cs := Finset.single_le_sum (f := fun b => |C b|) (fun j _ => abs_nonneg _)
            (Finset.mem_univ b)
      _ ≤ (⌈Cs⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (a₀ : ℝ) := by exact_mod_cast Nat.le_add_left _ _
  have hs0 : ∀ a : K → ℕ, 0 ≤ ∑ k, (a k : ℝ) := fun a => Finset.sum_nonneg (fun k _ => Nat.cast_nonneg _)
  have key : ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) → ∀ b, a₀ < a b →
      g a - g (Function.update a b (a b - 1)) =
        ((((hilbFn q (fun k => (a k : ℤ)) - hilbFn q ((fun k => (a k : ℤ)) - unitDeg b) : ℤ) : ℝ) -
          (intNum F q (Matrix.vecCons (unitDeg b) fun _ : Fin d => fun k => (a k : ℤ)) : ℝ) /
            d.factorial) -
        ((intNum F q (fun _ : Fin (d + 1) => fun k => (a k : ℤ)) -
            intNum F q (fun _ : Fin (d + 1) => (fun k => (a k : ℤ)) - unitDeg b) -
            ((d + 1 : ℕ) : ℤ) * intNum F q (Matrix.vecCons (unitDeg b) fun _ : Fin d => fun k => (a k : ℤ)) :
              ℤ) : ℝ) / ((d + 1).factorial : ℝ)) := by
    intro a ha b hb
    have hcast : (fun k => ((Function.update a b (a b - 1) k : ℕ) : ℤ)) =
        (fun k => (a k : ℤ)) - unitDeg b := by
      funext k
      by_cases hk : k = b
      · subst hk
        simp only [Function.update_self, Pi.sub_apply, unitDeg, Pi.single_eq_same]
        omega
      · simp [unitDeg, hk]
    have gfun : ∀ (c : K → ℕ) (y : K → ℤ), (fun k => (c k : ℤ)) = y →
        g c = (hilbFn q y : ℝ) - (intNum F q (fun _ : Fin (d + 1) => y) : ℝ) / ((d + 1).factorial : ℝ) := by
      intro c y h
      subst h
      rfl
    rw [gfun _ _ hcast, gfun a _ rfl]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  cases d with
  | zero =>
    have hempty : (Finset.univ.filter fun s : Finset (Fin (0 + 1)) => s.card + 2 ≤ 0 + 1) = ∅ := by
      ext s
      simp
    have hstep : ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) → ∀ b, a₀ < a b →
        |g a - g (Function.update a b (a b - 1))| ≤ 0 * ((∑ k, (a k : ℝ)) + 1) ^ 0 := by
      intro a ha b hb
      have hR := multilinear_step (ofPositionAdditive (intNum F q) hadd) hsym (fun k => (a k : ℤ)) (unitDeg b)
      rw [hempty, Finset.sum_empty, neg_zero] at hR
      simp only [ofPositionAdditive_apply] at hR
      have hIb := hAC b a (hAb a ha b)
      have hlt : |C b| < (∑ k, (a k : ℝ)) + 1 := by
        have h1 : (a₀ : ℝ) < a b := by exact_mod_cast hb
        have h2 : (a b : ℝ) ≤ ∑ k, (a k : ℝ) :=
          Finset.single_le_sum (f := fun k => (a k : ℝ)) (fun k _ => Nat.cast_nonneg _) (Finset.mem_univ b)
        linarith [hCb b]
      rw [key a ha b hb, hR]
      simp only [Nat.factorial_zero, Nat.cast_one, div_one, Int.cast_zero, zero_div, sub_zero] at hIb ⊢
      have hz := int_eq_of_abs_sub_le (hs0 a) hlt hIb
      rw [hz, sub_self]
      simp
    refine ⟨a₀, |g (fun _ => a₀)|, fun a ha => ?_⟩
    have hw := walk_bound g a₀ 0 le_rfl 0 hstep a ha
    have hexp : (((0 + 1 : ℕ) : ℝ) - 1) = 0 := by norm_num
    rw [hexp, Real.rpow_zero, mul_one]
    show |g a| ≤ _
    simpa using hw
  | succ n =>
    have hstep : ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) → ∀ b, a₀ < a b →
        |g a - g (Function.update a b (a b - 1))| ≤ (Cs + M) * ((∑ k, (a k : ℝ)) + 1) ^ n := by
      intro a ha b hb
      have hIb := hAC b a (hAb a ha b)
      have hRb := hE a b
      set s := ∑ k, (a k : ℝ) with hs
      have hexp : (((n + 1 : ℕ) : ℝ) - 1) = (n : ℝ) := by push_cast; ring
      rw [hexp, Real.rpow_natCast] at hIb
      have hRb' : |((intNum F q (fun _ : Fin (n + 1 + 1) => fun k => (a k : ℤ)) -
            intNum F q (fun _ : Fin (n + 1 + 1) => (fun k => (a k : ℤ)) - unitDeg b) -
            ((n + 1 + 1 : ℕ) : ℤ) * intNum F q (Matrix.vecCons (unitDeg b) fun _ : Fin (n + 1) => fun k => (a k : ℤ)) :
              ℤ) : ℝ)| ≤ (M : ℝ) * (s + 1) ^ n := by
        rw [← Int.cast_abs]
        have : ((M * ((∑ k, (a k : ℤ)) + 1) ^ (n + 1 - 1) : ℤ) : ℝ) = (M : ℝ) * (s + 1) ^ n := by
          rw [hs]
          push_cast
          rfl
        rw [← this]
        exact_mod_cast hRb
      rw [key a ha b hb]
      have hpos : (1 : ℝ) ≤ ((n + 1 + 1).factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hdiv : ∀ x : ℝ, |x / ((n + 1 + 1).factorial : ℝ)| ≤ |x| := by
        intro x
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < ((n + 1 + 1).factorial : ℝ))]
        exact div_le_self (abs_nonneg _) hpos
      have hCb' : C b * (s + 1) ^ n ≤ Cs * (s + 1) ^ n := by
        have hp : 0 ≤ (s + 1) ^ n := by positivity
        have : C b ≤ Cs := (le_abs_self _).trans
          (Finset.single_le_sum (f := fun b => |C b|) (fun j _ => abs_nonneg _) (Finset.mem_univ b))
        exact mul_le_mul_of_nonneg_right this hp
      refine (abs_sub _ _).trans ?_
      refine (add_le_add hIb ((hdiv _).trans hRb')).trans ?_
      linarith
    have hB : 0 ≤ Cs + (M : ℝ) := by
      have : 0 ≤ Cs := Finset.sum_nonneg (fun j _ => abs_nonneg _)
      have : (0 : ℝ) ≤ M := by exact_mod_cast hM0
      linarith
    refine ⟨a₀, |g (fun _ => a₀)| + (Cs + M), fun a ha => ?_⟩
    have hw := walk_bound g a₀ (Cs + M) hB n hstep a ha
    have hexp : (((n + 1 + 1 : ℕ) : ℝ) - 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hexp, Real.rpow_natCast]
    have h1 : (1 : ℝ) ≤ ((∑ k, (a k : ℝ)) + 1) ^ (n + 1) := one_le_pow₀ (by linarith [hs0 a])
    have h2 : |g (fun _ => a₀)| ≤ |g (fun _ => a₀)| * ((∑ k, (a k : ℝ)) + 1) ^ (n + 1) :=
      le_mul_of_one_le_right (abs_nonneg _) h1
    show |g a| ≤ _
    nlinarith
end GroundTheory.Heights₂.Heights.HilbertSamuel
