-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootGridLower_of_pos_62bab9c7db63
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:42:21.184374+00:00
-- url     : https://prove2.me/submissions/9e00843d-90cc-4c5b-8b00-2be592503f3a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootGridLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRootGridLower
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootGridLower_average_ed28bb99e416

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
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace RootGridLower
theorem _root_.solution {e M : ℕ} (hM : 0 < M) (Q : MvPolynomial (Fin e) ℤ) (hQ : Q ≠ 0)
    (hdeg : ∀ i, Q.degreeOf i < M) :
    ∃ ζ : Fin e → ℂ, (∀ i, ζ i ^ M = 1) ∧ 1 ≤ ‖eval ζ (map (Int.castRingHom ℂ) Q)‖ := by
  classical
  have hω := Complex.isPrimitiveRoot_exp M hM.ne'
  set ω := Complex.exp (2 * Real.pi * Complex.I / M)
  obtain ⟨j, hj⟩ : Q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]; exact hQ
  have hjM : ∀ i, j i < M := fun i => lt_of_le_of_lt (monomial_le_degreeOf i hj) (hdeg i)
  have hc : (1 : ℝ) ≤ ‖((Q.coeff j : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs (MvPolynomial.mem_support_iff.mp hj)
  have hω1 : ‖ω‖ = 1 := hω.norm'_eq_one hM.ne'
  by_contra hne
  push Not at hne
  have hlt : ∀ k : Fin e → Fin M,
      ‖eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q)‖ < 1 := by
    intro k
    refine hne _ fun i => ?_
    rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have hne' : (Finset.univ : Finset (Fin e → Fin M)).Nonempty :=
    ⟨fun i => ⟨j i, hjM i⟩, Finset.mem_univ _⟩
  have hupper : ‖(M : ℂ) ^ e * ((Q.coeff j : ℤ) : ℂ)‖ < (M : ℝ) ^ e := by
    rw [← RootGridLower.average hM hω Q hdeg j hjM]
    calc ‖∑ k : Fin e → Fin M, eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q) *
            ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ)‖
        ≤ ∑ k : Fin e → Fin M, ‖eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q) *
            ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ)‖ := norm_sum_le _ _
      _ = ∑ k : Fin e → Fin M, ‖eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q)‖ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp [norm_prod, hω1]
      _ < ∑ _k : Fin e → Fin M, (1 : ℝ) := Finset.sum_lt_sum_of_nonempty hne' fun k _ => hlt k
      _ = (M : ℝ) ^ e := by simp
  have hlower : (M : ℝ) ^ e ≤ ‖(M : ℂ) ^ e * ((Q.coeff j : ℤ) : ℂ)‖ := by
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    exact le_mul_of_one_le_right (by positivity) hc
  linarith
end RootGridLower
end GroundTheory.Heights₂.Heights.HilbertSamuel
