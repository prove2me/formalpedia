-- Prove2me | solution 1 for PI.VolStabS.FFHS.frob_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:50:40.231926+00:00
-- url     : https://prove2.me/submissions/dcf039ed-0c4d-410d-80cc-17e90bfaf689

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
private theorem add_pow_card_eq_add_pow_card (a b : K) :
    (a + b) ^ Fintype.card k = a ^ Fintype.card k + b ^ Fintype.card k := by
  obtain ⟨p, hp⟩ := CharP.exists k
  obtain ⟨n, hprime, hn⟩ := FiniteField.card k p
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  rw [hn]
  exact add_pow_char_pow a b p (n : ℕ)
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
theorem _root_.solution (σ : K ≃ₐ[k] K) (h2 : finrank k K = 2) (hne : σ ≠ AlgEquiv.refl) :
    ∀ x, σ x = x ^ Fintype.card k := by
  have hK := card_eq_card_sq_of_finrank_two (k := k) (K := K) h2
  have hqq : ∀ y : K, (y ^ Fintype.card k) ^ Fintype.card k = y := fun y => by
    rw [← pow_mul, ← sq, ← hK, FiniteField.pow_card]
  have hfix : ∀ c : K, c ^ Fintype.card k = c → σ c = c := by
    intro c hc
    obtain ⟨d0, rfl⟩ := mem_range_algebraMap_of_pow_card_eq c hc
    exact σ.commutes d0
  have hdich : ∀ x : K, σ x = x ∨ σ x = x ^ Fintype.card k := by
    intro x
    have hs : σ x + σ x ^ Fintype.card k = x + x ^ Fintype.card k := by
      rw [← map_pow, ← map_add]
      exact hfix _ (by rw [add_pow_card_eq_add_pow_card, hqq, add_comm])
    have hm : σ x * σ x ^ Fintype.card k = x * x ^ Fintype.card k := by
      rw [← map_pow, ← map_mul]
      exact hfix _ (by rw [mul_pow, hqq, mul_comm])
    have h0 : (σ x - x) * (σ x - x ^ Fintype.card k) = 0 := by
      linear_combination σ x * hs - hm
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  intro x
  by_contra ha
  have hq0 : Fintype.card k ≠ 0 := Fintype.card_ne_zero
  have hax : σ x = x := (hdich x).resolve_right ha
  obtain ⟨b, hb⟩ : ∃ b, σ b ≠ b := by
    by_contra hcon
    push_neg at hcon
    exact hne (AlgEquiv.ext fun y => by simpa using hcon y)
  have hbq : σ b = b ^ Fintype.card k := (hdich b).resolve_left hb
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact ha (by rw [map_zero, zero_pow hq0])
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (map_zero σ)
  rcases hdich (x * b) with h | h
  · rw [map_mul, hax, hbq] at h
    exact hb (hbq.trans (mul_left_cancel₀ hx0 h))
  · rw [map_mul, hax, hbq, mul_pow] at h
    exact ha (hax.trans (mul_right_cancel₀ (pow_ne_zero _ hb0) h))
end PI.VolStabS.FFHS
