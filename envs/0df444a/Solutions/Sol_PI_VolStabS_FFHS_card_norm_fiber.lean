-- Prove2me | solution 1 for PI.VolStabS.FFHS.card_norm_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:50:21.049224+00:00
-- url     : https://prove2.me/submissions/50ff65cb-ac39-4206-bf29-336ecb308b6d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFCnt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFIn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.VolStabS.FFHS
open Module Polynomial
section matrix
variable {K : Type} [Field K] {σ : K →+* K}
end matrix
section field
variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]
private theorem card_eq_card_sq_of_finrank_two (h2 : finrank k K = 2) :
    Fintype.card K = Fintype.card k ^ 2 := by
  rw [← h2]
  exact Module.card_eq_pow_finrank
private theorem mem_range_algebraMap_of_pow_card_eq (d : K) (hd : d ^ Fintype.card k = d) :
    ∃ d0 : k, algebraMap k K d0 = d := by
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hP : (X ^ Fintype.card k - X : K[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq1
  have hsub : Finset.univ.image (algebraMap k K) ⊆
      (X ^ Fintype.card k - X : K[X]).roots.toFinset := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def, eval_sub, eval_pow, eval_X, ← map_pow,
      FiniteField.pow_card, sub_self]
  have hcard : (X ^ Fintype.card k - X : K[X]).roots.toFinset.card ≤
      (Finset.univ.image (algebraMap k K)).card := by
    rw [Finset.card_image_of_injective _ (algebraMap k K).injective, Finset.card_univ]
    calc _ ≤ Multiset.card (X ^ Fintype.card k - X : K[X]).roots := Multiset.toFinset_card_le _
      _ ≤ (X ^ Fintype.card k - X : K[X]).natDegree := card_roots' _
      _ = Fintype.card k := FiniteField.X_pow_card_sub_X_natDegree_eq K hq1
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : d ∈ (X ^ Fintype.card k - X : K[X]).roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def, eval_sub, eval_pow, eval_X, hd, sub_self]
  rw [← heq] at hmem
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hmem
  exact ⟨y, hy⟩
end field
end PI.VolStabS.FFHS
end
end

set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.FFHS
open Module Polynomial
variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]
namespace PI.VolStabS.FFHS
theorem _root_.solution (σ : K ≃ₐ[k] K) (hfrob : ∀ x, σ x = x ^ Fintype.card k)
    (h2 : finrank k K = 2) (d : K) (hd : σ d = d) :
    Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else Fintype.card k + 1 := by
  by_cases hd0 : d = 0
  · subst hd0
    rw [if_pos rfl, Nat.card_eq_one_iff_exists]
    refine ⟨⟨0, by simp⟩, fun y => Subtype.ext ?_⟩
    rcases mul_eq_zero.mp y.2 with h | h
    · exact h
    · exact (map_eq_zero σ).mp h
  rw [if_neg hd0]
  have hK := card_eq_card_sq_of_finrank_two (k := k) (K := K) h2
  have hqq : ∀ y : K, (y ^ Fintype.card k) ^ Fintype.card k = y := fun y => by
    rw [← pow_mul, ← sq, ← hK, FiniteField.pow_card]
  have hN : ∀ t : K, t * σ t = t ^ (Fintype.card k + 1) := fun t => by
    rw [hfrob, pow_succ']
  have hfixset : Finset.univ.filter (fun e : K => σ e = e) =
      Finset.univ.image (algebraMap k K) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro he
      exact mem_range_algebraMap_of_pow_card_eq e ((hfrob e).symm.trans he)
    · rintro ⟨y, rfl⟩
      exact σ.commutes y
  have hfixcard : (Finset.univ.filter (fun e : K => σ e = e)).card = Fintype.card k := by
    rw [hfixset, Finset.card_image_of_injective _ (algebraMap k K).injective, Finset.card_univ]
  have hD : (Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0)).card + 1 = Fintype.card k := by
    have hset : Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0) =
        (Finset.univ.filter (fun e : K => σ e = e)).erase 0 := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      exact and_comm
    rw [hset, Finset.card_erase_add_one (by simp), hfixcard]
  have hS : (Finset.univ.filter (fun t : K => t ≠ 0)).card + 1 = Fintype.card k ^ 2 := by
    rw [Finset.filter_ne', Finset.card_erase_add_one (Finset.mem_univ _), Finset.card_univ, hK]
  have hmaps : ∀ t ∈ Finset.univ.filter (fun t : K => t ≠ 0),
      t * σ t ∈ Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    refine ⟨?_, mul_ne_zero ht ((map_ne_zero σ).mpr ht)⟩
    rw [map_mul, hfrob (σ t), hfrob t, hqq, mul_comm]
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  have hbound : ∀ e : K, ((Finset.univ.filter (fun t : K => t ≠ 0)).filter
      (fun t => t * σ t = e)).card ≤ Fintype.card k + 1 := by
    intro e
    calc _ ≤ (nthRoots (Fintype.card k + 1) e).toFinset.card := by
          apply Finset.card_le_card
          intro t ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
          rw [Multiset.mem_toFinset, mem_nthRoots (Nat.succ_pos _), ← hN]
          exact ht.2
      _ ≤ Multiset.card (nthRoots (Fintype.card k + 1) e) := Multiset.toFinset_card_le _
      _ ≤ Fintype.card k + 1 := card_nthRoots _ _
  have htarget : Nat.card {t : K // t * σ t = d} =
      ((Finset.univ.filter (fun t : K => t ≠ 0)).filter (fun t => t * σ t = d)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ht
      refine ⟨?_, ht⟩
      rintro rfl
      exact hd0 (by simpa using ht.symm)
    · exact fun ht => ht.2
  rw [htarget]
  refine le_antisymm (hbound d) (not_lt.mp fun hlt => ?_)
  have hdD : d ∈ Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0) := by
    simp [hd, hd0]
  have hlt2 : (Finset.univ.filter (fun t : K => t ≠ 0)).card <
      (Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0)).card * (Fintype.card k + 1) := by
    calc (Finset.univ.filter (fun t : K => t ≠ 0)).card = _ := hsum
      _ < ∑ e ∈ Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0), (Fintype.card k + 1) :=
          Finset.sum_lt_sum (fun e _ => hbound e) ⟨d, hdD, hlt⟩
      _ = _ := by rw [Finset.sum_const, smul_eq_mul]
  rw [← hD] at hS hlt2
  nlinarith [hS, hlt2]
end PI.VolStabS.FFHS
