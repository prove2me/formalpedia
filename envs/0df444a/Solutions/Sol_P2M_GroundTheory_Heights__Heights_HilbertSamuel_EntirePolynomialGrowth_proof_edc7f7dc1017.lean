-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_EntirePolynomialGrowth_proof_edc7f7dc1017
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:56:05.244129+00:00
-- url     : https://prove2.me/submissions/06a14143-b365-42f3-a3b3-ef5ef054bbaf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StEntirePolynomialGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PEntirePolynomialGrowth
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_entire_polynomialGrowth_one_var_410c9b15615f

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
open MvPolynomial Metric
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace EntirePolynomialGrowth
theorem _root_.solution : EntirePolynomialGrowth.Statement := by
  intro d
  induction d with
  | zero =>
    intro f C M _ _
    refine ⟨MvPolynomial.C (f 0), fun y => ?_⟩
    rw [MvPolynomial.eval_C]
    congr 1
    exact Subsingleton.elim _ _
  | succ d ih =>
    intro f C M hf hb
    set C' := max C 0 with hC'def
    have hC' : 0 ≤ C' := le_max_right _ _
    have hb' : ∀ y, ‖f y‖ ≤ C' * (1 + ‖y‖) ^ M := fun y =>
      (hb y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hcons : ∀ (c : ℂ) (w : Fin d → ℂ), ‖(Fin.cons c w : Fin (d + 1) → ℂ)‖ ≤ ‖c‖ + ‖w‖ := by
      intro c w
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [norm_nonneg]
      · simp only [Fin.cons_succ]
        linarith [norm_le_pi_norm w i, norm_nonneg c]
    have hdc : ∀ w : Fin d → ℂ, Differentiable ℂ (fun z : ℂ => (Fin.cons z w : Fin (d + 1) → ℂ)) := by
      intro w
      refine differentiable_pi.2 fun i => ?_
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero]; fun_prop
      · simp only [Fin.cons_succ]; fun_prop
    have hdw : ∀ c : ℂ, Differentiable ℂ (fun w : Fin d → ℂ => (Fin.cons c w : Fin (d + 1) → ℂ)) := by
      intro c
      refine differentiable_pi.2 fun i => ?_
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero]; fun_prop
      · simp only [Fin.cons_succ]; fun_prop
    have hp : ∀ j : ℕ, ∃ p : MvPolynomial (Fin d) ℂ,
        ∀ w, f (Fin.cons (j : ℂ) w) = eval w p := by
      intro j
      refine ih _ (C' * (1 + (j : ℝ)) ^ M) M (hf.comp (hdw _)) fun w => ?_
      have hn := hcons (j : ℂ) w
      rw [Complex.norm_natCast] at hn
      calc ‖f (Fin.cons (j : ℂ) w)‖
          ≤ C' * (1 + ‖(Fin.cons (j : ℂ) w : Fin (d + 1) → ℂ)‖) ^ M := hb' _
        _ ≤ C' * ((1 + (j : ℝ)) * (1 + ‖w‖)) ^ M := by
            gcongr
            nlinarith [norm_nonneg w, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
        _ = C' * (1 + (j : ℝ)) ^ M * (1 + ‖w‖) ^ M := by rw [mul_pow, mul_assoc]
    choose p hp using hp
    have hz : ∀ w : Fin d → ℂ, ∃ q : Polynomial ℂ, q.natDegree ≤ M ∧
        ∀ z, f (Fin.cons z w) = q.eval z := by
      intro w
      refine entire_polynomialGrowth_one_var M _ (C' * (1 + ‖w‖) ^ M) (hf.comp (hdc w)) fun z => ?_
      have hn := hcons z w
      calc ‖f (Fin.cons z w)‖ ≤ C' * (1 + ‖(Fin.cons z w : Fin (d + 1) → ℂ)‖) ^ M := hb' _
        _ ≤ C' * ((1 + ‖w‖) * (1 + ‖z‖)) ^ M := by
            gcongr
            nlinarith [norm_nonneg w, norm_nonneg z]
        _ = C' * (1 + ‖w‖) ^ M * (1 + ‖z‖) ^ M := by rw [mul_pow, mul_assoc]
    refine ⟨∑ j ∈ Finset.range (M + 1),
      Polynomial.aeval (X 0 : MvPolynomial (Fin (d + 1)) ℂ)
        (Lagrange.basis (Finset.range (M + 1)) (fun j : ℕ => (j : ℂ)) j) * rename Fin.succ (p j),
      fun y => ?_⟩
    obtain ⟨q, hqd, hq⟩ := hz (Fin.tail y)
    have hinj : Set.InjOn (fun j : ℕ => (j : ℂ)) (Finset.range (M + 1) : Set ℕ) :=
      Nat.cast_injective.injOn
    have hdeg : q.degree < (Finset.range (M + 1)).card := by
      rw [Finset.card_range]
      exact (Polynomial.degree_le_of_natDegree_le hqd).trans_lt (by exact_mod_cast Nat.lt_succ_self M)
    have key := Lagrange.eq_interpolate hinj hdeg
    have hev : ∀ P : Polynomial ℂ,
        eval y (Polynomial.aeval (X 0 : MvPolynomial (Fin (d + 1)) ℂ) P) = P.eval (y 0) := by
      intro P
      have hid : (eval y).comp (algebraMap ℂ (MvPolynomial (Fin (d + 1)) ℂ)) = RingHom.id ℂ := by
        ext; simp
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂, MvPolynomial.eval_X, hid]
      rfl
    conv_lhs => rw [← Fin.cons_self_tail y, hq (y 0), key]
    rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hev, eval_rename, Polynomial.eval_mul, Polynomial.eval_C, ← hq, hp, mul_comm]
    rfl
end EntirePolynomialGrowth
end GroundTheory.Heights₂.Heights.HilbertSamuel
