-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.one_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:18:59.313907+00:00
-- url     : https://prove2.me/submissions/f99b49a7-e37e-4ad5-b4be-b65331971582

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DecompBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SupportFreeOfBlockSubstInvariant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_coeff_compB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_scaleBlock_eq_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_sigF_alg
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K : Type} [Field K] [CharZero K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (b : Fin (D + 1)) (z : KTf K D N)
    (hz : ∀ u : Kˣ, sigF (K := K) (D := D) (N := N) b u z = z)
    (p q : KTp K D N) (hq : q ≠ 0)
    (hpq : algebraMap (KTp K D N) (KTf K D N) p = z * algebraMap (KTp K D N) (KTf K D N) q) :
    ∃ k, compB b k q ≠ 0 ∧ algebraMap (KTp K D N) (KTf K D N) (compB b k p) =
      z * algebraMap (KTp K D N) (KTf K D N) (compB b k q) := by
  obtain ⟨M, hMp, hMq⟩ : ∃ M, (∀ s ∈ p.support, degB b s < M) ∧ (∀ s ∈ q.support, degB b s < M) :=
    ⟨(p.support ∪ q.support).sup (degB b) + 1,
      fun s hs => Nat.lt_succ_of_le (Finset.le_sup (f := degB b) (Finset.mem_union_left _ hs)),
      fun s hs => Nat.lt_succ_of_le (Finset.le_sup (f := degB b) (Finset.mem_union_right _ hs))⟩
  have hroot : ∀ u : Kˣ, ∑ k ∈ Finset.range M,
      (algebraMap (KTp K D N) (KTf K D N) (compB b k p) - z * algebraMap (KTp K D N) (KTf K D N) (compB b k q)) * (algebraMap (KTp K D N) (KTf K D N) (C (u : K))) ^ k = 0 := by
    intro u
    have h1 := congrArg (sigF (K := K) (D := D) (N := N) b u) hpq
    rw [map_mul, sigF_alg, sigF_alg, hz u, scaleBlock_eq_sum b u p M hMp, scaleBlock_eq_sum b u q M hMq,
      map_sum, map_sum, Finset.mul_sum] at h1
    have h2 := sub_eq_zero.mpr h1
    rw [← Finset.sum_sub_distrib] at h2
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h2
    simp only [map_mul, map_pow]
    ring
  have hQ : (∑ k ∈ Finset.range M, Polynomial.monomial k
      (algebraMap (KTp K D N) (KTf K D N) (compB b k p) - z * algebraMap (KTp K D N) (KTf K D N) (compB b k q))) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => algebraMap (KTp K D N) (KTf K D N) (C ((n : K) + 1))) ?_ ?_
    · intro n m hnm
      have h2 := IsFractionRing.injective (KTp K D N) (KTf K D N) hnm
      have h3 := MvPolynomial.C_injective (TVar D N) K h2
      exact_mod_cast add_right_cancel h3
    · intro n
      have hu := hroot (Units.mk0 ((n : K) + 1) (Nat.cast_add_one_ne_zero n))
      rw [Units.val_mk0] at hu
      show Polynomial.eval _ _ = 0
      rw [Polynomial.eval_finset_sum]
      simp only [Polynomial.eval_monomial]
      exact hu
  have hcoef : ∀ k < M, algebraMap (KTp K D N) (KTf K D N) (compB b k p) - z * algebraMap (KTp K D N) (KTf K D N) (compB b k q) = 0 := by
    intro k hk
    have h4 := congrArg (fun P => Polynomial.coeff P k) hQ
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at h4
    first
    | rwa [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hk)] at h4
    | rwa [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hk)] at h4
  have hqs : q = ∑ k ∈ Finset.range M, compB b k q := by
    ext t
    rw [MvPolynomial.coeff_sum]
    simp only [coeff_compB]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra hne
      exact h (Finset.mem_range.mpr (hMq t (MvPolynomial.mem_support_iff.mpr hne)))
  obtain ⟨k, hk, hqk⟩ : ∃ k ∈ Finset.range M, compB b k q ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hq
    rw [hqs]
    exact Finset.sum_eq_zero hc
  exact ⟨k, hqk, sub_eq_zero.mp (hcoef k (Finset.mem_range.mp hk))⟩
end ReciprocityTheory.ChartRestriction.G.T0
