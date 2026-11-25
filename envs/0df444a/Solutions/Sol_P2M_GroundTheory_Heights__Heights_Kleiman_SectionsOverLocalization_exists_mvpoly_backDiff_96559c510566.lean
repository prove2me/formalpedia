-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_mvpoly_backDiff_96559c510566
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:08:12.868126+00:00
-- url     : https://prove2.me/submissions/642e6e2a-f917-43ac-a399-7b67947de8eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsRestBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsPolyBackDiffPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_poly_backDiff_pow_32b050b07dc7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
theorem _root_.solution {K : Type} [DecidableEq K] (k : K) (q : MvPolynomial K ℚ) :
    ∃ R : MvPolynomial K ℚ, ∀ x : K → ℚ, eval x R - eval (x - Pi.single k 1) R = eval x q := by
  induction q using MvPolynomial.induction_on' with
  | monomial u a =>
    obtain ⟨P, hP⟩ := exists_poly_backDiff_pow (u k)
    refine ⟨monomial (u.erase k) a * Polynomial.aeval (X k : MvPolynomial K ℚ) P, fun x => ?_⟩
    have hm : ∀ y : K → ℚ, (∀ i, i ≠ k → y i = x i) →
        eval y (monomial (u.erase k) a) = eval x (monomial (u.erase k) a) := by
      intro y hy
      simp only [eval_monomial]
      congr 1
      apply Finsupp.prod_congr
      intro i hi
      rw [Finsupp.support_erase, Finset.mem_erase] at hi
      rw [hy i hi.1]
    have hP' : ∀ y : K → ℚ, eval y (Polynomial.aeval (X k : MvPolynomial K ℚ) P) = P.eval (y k) := by
      intro y
      clear hP
      induction P using Polynomial.induction_on' with
      | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
      | monomial n c => simp [Polynomial.aeval_monomial]
    have hu : monomial u a = monomial (u.erase k) a * X k ^ (u k) := by
      rw [X_pow_eq_monomial, monomial_mul, mul_one, add_comm, Finsupp.single_add_erase]
    have hy : ∀ i, i ≠ k → (x - Pi.single k (1 : ℚ) : K → ℚ) i = x i := by
      intro i hi
      simp [hi]
    rw [hu, map_mul, map_mul, map_mul, hm _ hy, hP', hP', map_pow, eval_X]
    have hk : (x - Pi.single k (1 : ℚ) : K → ℚ) k = x k - 1 := by simp
    rw [hk]
    linear_combination (eval x (monomial (u.erase k) a)) * hP (x k)
  | add p q hp hq =>
    obtain ⟨R₁, h₁⟩ := hp
    obtain ⟨R₂, h₂⟩ := hq
    exact ⟨R₁ + R₂, fun x => by simp only [map_add]; linear_combination h₁ x + h₂ x⟩
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
