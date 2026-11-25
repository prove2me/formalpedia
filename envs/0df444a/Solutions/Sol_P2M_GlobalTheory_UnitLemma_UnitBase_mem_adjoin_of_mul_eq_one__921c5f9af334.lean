-- Prove2me | solution 1 for P2M_GlobalTheory_UnitLemma_UnitBase_mem_adjoin_of_mul_eq_one__921c5f9af334
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:17.726903+00:00
-- url     : https://prove2.me/submissions/f8831887-19fb-4df3-aa44-7e6f260912ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnitBase
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.UnitBase
theorem _root_.solution {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {s t : A}
    (h : s * t = 1) (ht : IsIntegral O t) : t ∈ Algebra.adjoin O {s} := by
  obtain ⟨p, hp, hpt⟩ := ht
  have e : aeval t p = 0 := hpt
  rw [aeval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_smul] at e
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [h0] at e
    simp at e
    have : t = 0 := by simpa using congrArg (t * ·) e
    rw [this]; exact Subalgebra.zero_mem _
  obtain ⟨k, hk⟩ : ∃ k, p.natDegree = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hk] at e
  have hts : t * s = 1 := by rw [mul_comm]; exact h
  have h1 : t ^ (k + 1) * s ^ k = t := by
    rw [pow_succ', mul_assoc, ← mul_pow, hts, one_pow, mul_one]
  have h2 : ∀ i ∈ Finset.range (k + 1), p.coeff i • t ^ i * s ^ k = p.coeff i • s ^ (k - i) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [smul_mul_assoc]
    congr 1
    rw [show s ^ k = s ^ i * s ^ (k - i) by rw [← pow_add, Nat.add_sub_cancel' hik], ← mul_assoc,
      ← mul_pow, hts, one_pow, one_mul]
  have e2 := congrArg (· * s ^ k) e
  simp only [add_mul, zero_mul, Finset.sum_mul] at e2
  rw [Finset.sum_congr rfl h2, h1] at e2
  have key : t = -∑ i ∈ Finset.range (k + 1), p.coeff i • s ^ (k - i) := by
    linear_combination e2
  rw [key]
  exact Subalgebra.neg_mem _ (Subalgebra.sum_mem _ fun i _ =>
    Subalgebra.smul_mem _ (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton O s) _) _)
end GlobalTheory.UnitLemma.UnitBase
