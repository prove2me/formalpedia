-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_multilinear_step_le_873981ad91dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:16:13.374528+00:00
-- url     : https://prove2.me/submissions/54c9fa97-2fe1-4585-a9fd-825980ea4a64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_multilinear_abs_le_d574a8201a0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_multilinear_step_8d3b99047953

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
theorem _root_.solution {d : ℕ} (f : MultilinearMap ℤ (fun _ : Fin (d + 1) => K → ℤ) ℤ)
    (hsym : ∀ (σ : Equiv.Perm (Fin (d + 1))) (m : Fin (d + 1) → K → ℤ), f (m ∘ σ) = f m) :
    ∃ M : ℤ, 0 ≤ M ∧ ∀ (a : K → ℕ) (b : K),
      |f (fun _ => fun k => (a k : ℤ)) - f (fun _ => (fun k => (a k : ℤ)) - unitDeg b) -
          ((d + 1 : ℕ) : ℤ) * f (Matrix.vecCons (unitDeg b) fun _ : Fin d => fun k => (a k : ℤ))| ≤
        M * ((∑ k, (a k : ℤ)) + 1) ^ (d - 1) := by
  obtain ⟨M₀, hM₀, hbd⟩ := multilinear_abs_le f
  refine ⟨(Fintype.card (Finset (Fin (d + 1))) : ℤ) * M₀, by positivity, ?_⟩
  intro a b
  set S : ℤ := ∑ k, (a k : ℤ)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k _ => Nat.cast_nonneg _)
  rw [multilinear_step f hsym, abs_neg]
  have hterm : ∀ s ∈ Finset.univ.filter (fun s : Finset (Fin (d + 1)) => s.card + 2 ≤ d + 1),
      |f (s.piecewise (fun _ => fun k => (a k : ℤ)) (fun _ => -unitDeg b))| ≤ M₀ * (S + 1) ^ (d - 1) := by
    intro s hs
    have hcard : s.card ≤ d - 1 := by
      have := (Finset.mem_filter.mp hs).2
      omega
    refine (hbd _).trans (mul_le_mul_of_nonneg_left ?_ hM₀)
    have hprod : (∏ i, ∑ k, |(s.piecewise (fun _ => fun k => (a k : ℤ)) (fun _ => -unitDeg b)) i k|) =
        ∏ i, (if i ∈ s then S else 1) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      by_cases hi : i ∈ s
      · rw [Finset.piecewise_eq_of_mem _ _ _ hi, if_pos hi]
        exact Finset.sum_congr rfl (fun k _ => abs_of_nonneg (Nat.cast_nonneg _))
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hi, if_neg hi]
        simp [unitDeg, Pi.single_apply, apply_ite]
    rw [hprod, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
    calc S ^ s.card ≤ (S + 1) ^ s.card := pow_le_pow_left₀ hS (by linarith) _
      _ ≤ (S + 1) ^ (d - 1) := pow_le_pow_right₀ (by linarith) hcard
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact_mod_cast (Finset.card_filter_le _ _).trans (le_of_eq Finset.card_univ)
end GroundTheory.Heights₂.Heights.HilbertSamuel
