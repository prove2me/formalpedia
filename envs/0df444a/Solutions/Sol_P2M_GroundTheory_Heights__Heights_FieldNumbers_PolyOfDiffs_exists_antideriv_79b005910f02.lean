-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_exists_antideriv_79b005910f02
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:27:26.963801+00:00
-- url     : https://prove2.me/submissions/839f231a-4132-4744-9161-3d6ee328f3cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_exists_pow_antideriv_69ad4af11f37
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_eval_aeval_X_223dfec544ec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
open GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
variable {K : Type}
variable [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
theorem _root_.solution (k : K) (q : MvPolynomial K ℚ) : ∃ P : MvPolynomial K ℚ,
    P.totalDegree ≤ q.totalDegree + 1 ∧
    ∀ x : K → ℚ, eval x P - eval (x - Pi.single k 1) P = eval x q := by
  have key : ∀ α ∈ q.support, ∃ P : MvPolynomial K ℚ, P.totalDegree ≤ q.totalDegree + 1 ∧
      ∀ x : K → ℚ, eval x P - eval (x - Pi.single k 1) P = eval x (monomial α (q.coeff α)) := by
    intro α hα
    obtain ⟨F, hFd, hF⟩ := exists_pow_antideriv (α k)
    refine ⟨monomial (α.erase k) (q.coeff α) * Polynomial.aeval (X k) F, ?_, fun x => ?_⟩
    · have hsum : ((α.erase k).sum fun _ e => e) + α k ≤ q.totalDegree := by
        refine le_trans (le_of_eq ?_) (le_totalDegree hα)
        conv_rhs => rw [← Finsupp.single_add_erase k α]
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
          Finsupp.sum_single_index rfl, add_comm]
      have h1 : (monomial (α.erase k) (q.coeff α)).totalDegree ≤
          (α.erase k).sum fun _ e => e := totalDegree_monomial_le _ _
      have h2 : (Polynomial.aeval (X k : MvPolynomial K ℚ) F).totalDegree ≤ α k + 1 := by
        rw [Polynomial.aeval_eq_sum_range]
        refine totalDegree_finsetSum_le fun i hi => ?_
        refine (totalDegree_smul_le _ _).trans ?_
        rw [totalDegree_X_pow]
        exact (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hFd
      refine (totalDegree_mul _ _).trans ?_
      omega
    · have hmono : monomial α (q.coeff α) = monomial (α.erase k) (q.coeff α) * X k ^ (α k) := by
        rw [X_pow_eq_monomial, monomial_mul, mul_one, add_comm, Finsupp.single_add_erase]
      have hsh : eval (x - Pi.single k 1) (monomial (α.erase k) (q.coeff α)) =
          eval x (monomial (α.erase k) (q.coeff α)) := by
        simp only [eval_monomial]
        congr 1
        refine Finsupp.prod_congr fun j hj => ?_
        have hjk : j ≠ k := by
          rw [Finsupp.support_erase] at hj
          exact (Finset.mem_erase.1 hj).1
        simp [Pi.single_apply, hjk]
      have hev : ∀ y : K → ℚ, eval y (Polynomial.aeval (X k) F) = F.eval (y k) :=
        fun y => eval_aeval_X y k F
      rw [hmono, map_mul, map_mul, hsh, hev, hev, map_mul, map_pow, eval_X, ← mul_sub]
      congr 1
      rw [← hF (x k)]
      simp
  choose! P hPd hPe using key
  refine ⟨∑ α ∈ q.support, P α, totalDegree_finsetSum_le hPd, fun x => ?_⟩
  conv_rhs => rw [q.as_sum]
  simp only [map_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun α hα => hPe α hα x
end GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
