-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.poly_of_rot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:09:03.564679+00:00
-- url     : https://prove2.me/submissions/91845b14-a57c-46d7-b336-21f60a5b47f7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivScale
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_iteratedDeriv_rel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Nat
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
namespace PositivityTheory.SiegelWeilFormula.KFPB
theorem _root_.solution (q : Polynomial ℂ) (hq : q ≠ 0) (μ ω : ℂ) (hμ : μ ≠ 0) (hω0 : ω ≠ 0)
    (hω : ∀ j : ℕ, 0 < j → ω ^ j ≠ 1) :
    ∃ N : ℕ, ∀ E : ℂ → ℂ, Differentiable ℂ E →
      (∀ z, ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * μ ^ i * E (ω ^ i * z) = 0) →
      ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧ ∀ z, E z = p.eval z := by
  have hlt : ∀ a b : ℕ, a < b → ω ^ a ≠ ω ^ b := by
    intro a b h hab
    apply hω (b - a) (Nat.sub_pos_of_lt h)
    apply mul_left_cancel₀ (pow_ne_zero a hω0)
    rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, hab]
  have hinj : Function.Injective fun j : ℕ => μ * ω ^ j := by
    intro a b hab
    have hab' : ω ^ a = ω ^ b := mul_left_cancel₀ hμ hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt a b h hab'
    · exact hlt b a h hab'.symm
  have hfin : {j : ℕ | q.eval (μ * ω ^ j) = 0}.Finite := by
    apply Set.Finite.of_finite_image _ hinj.injOn
    apply (q.roots.toFinset.finite_toSet).subset
    rintro _ ⟨j, hj, rfl⟩
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_roots hq).2 hj
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N, fun E hE hrel => ?_⟩
  have hvan : ∀ j, N < j → iteratedDeriv j E 0 = 0 := by
    intro j hj
    have h0 : (fun z => ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * μ ^ i * E (ω ^ i * z)) = 0 :=
      funext hrel
    have h1 := PositivityTheory.SiegelWeilFormula.KFPB.iteratedDeriv_rel q μ ω E hE j
    rw [h0, iteratedDeriv_const_zero] at h1
    rcases mul_eq_zero.1 h1.symm with h | h
    · exact absurd (hN h) (not_le.2 hj)
    · exact h
  refine ⟨∑ n ∈ Finset.range (N + 1),
      Polynomial.C ((n ! : ℂ)⁻¹ * iteratedDeriv n E 0) * Polynomial.X ^ n, ?_, fun z => ?_⟩
  · exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun n hn =>
      (Polynomial.natDegree_C_mul_X_pow_le _ n).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))
  · have hs := Complex.hasSum_taylorSeries_of_entire hE 0 z
    refine (hs.unique (hasSum_sum_of_ne_finset_zero (s := Finset.range (N + 1)) ?_)).trans ?_
    · intro m hm
      simp only [Finset.mem_range, not_lt] at hm
      simp [hvan m (by omega)]
    · rw [Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        smul_eq_mul, sub_zero]
      ring
end PositivityTheory.SiegelWeilFormula.KFPB
