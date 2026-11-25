-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.wa_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:56:45.777192+00:00
-- url     : https://prove2.me/submissions/d0b49265-2993-4114-b807-fa713795a7b8

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_cases3
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_waExt_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_waExt_last
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_waExt_mid
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_witt_apply
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_waR_apply
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_diag
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_finrank_inf_ker
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_hyp
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_perp_nondeg
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_sum_left
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_sum_right
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_symm
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_zero_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.waExt_zero
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.waExt_last
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.waExt_mid

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) :
    ∀ (n : ℕ) (W : Submodule K (Fin r → K)), finrank K W = n →
      (∀ x ∈ W, (∀ y ∈ W, S.h x y = 0) → x = 0) →
      ∃ (m : ℕ) (b : Fin n → Fin r → K) (g : Fin n → K), (∀ i, b i ∈ W) ∧ 2 * m ≤ n ∧
        (∀ i j, S.h (b i) (b j) = wittMat n m g i j) ∧
        ∀ t : Fin n → K, (∀ i : Fin n, (i : ℕ) < m ∨ n ≤ (i : ℕ) + m → t i = 0) →
          ∑ i, S.c (t i) * g i * t i = 0 → t = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hW hnd
  by_cases hiso : ∃ x ∈ W, x ≠ 0 ∧ S.h x x = 0
  · obtain ⟨x, hxW, hx0, hxx⟩ := hiso
    obtain ⟨y, hyW, hxy, hyy⟩ := wa_hyp S W hnd x hxW hx0 hxx
    have hyx : S.h y x = 1 := by rw [wa_symm, hxy, map_one]
    have hf1 := wa_finrank_inf_ker W (waR S x) y hyW
      (by rw [waR_apply, hxy]; exact one_ne_zero)
    have hf2 := wa_finrank_inf_ker (W ⊓ LinearMap.ker (waR S x)) (waR S y) x
      (Submodule.mem_inf.mpr ⟨hxW, by rw [LinearMap.mem_ker, waR_apply, hxx]⟩)
      (by rw [waR_apply, hyx]; exact one_ne_zero)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 :=
      ⟨finrank K ↥(W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y)), by omega⟩
    obtain ⟨m', b', g', hb'W, hm', hgram', hani'⟩ := ih n' (by omega)
      (W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y)) (by omega)
      (wa_perp_nondeg S W hnd x y hxW hyW hxx hxy hyy)
    have hmem : ∀ j, b' j ∈ W ∧ S.h x (b' j) = 0 ∧ S.h y (b' j) = 0 := fun j => by
      have h := hb'W j
      rw [Submodule.mem_inf, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, waR_apply,
        waR_apply] at h
      exact ⟨h.1.1, h.1.2, h.2⟩
    have hbx : ∀ j, S.h (b' j) x = 0 := fun j => by rw [wa_symm, (hmem j).2.1, map_zero]
    have hby : ∀ j, S.h (b' j) y = 0 := fun j => by rw [wa_symm, (hmem j).2.2, map_zero]
    refine ⟨m' + 1, waExt x y b', waExt 0 0 g', fun i => ?_, by omega, fun i j => ?_,
      fun t ht hsum => ?_⟩
    · rcases wa_cases3 i with rfl | rfl | ⟨j, rfl⟩
      · simpa using hxW
      · simpa using hyW
      · simpa using (hmem j).1
    · rw [wa_witt_apply]
      rcases wa_cases3 i with rfl | rfl | ⟨i, rfl⟩ <;>
        rcases wa_cases3 j with rfl | rfl | ⟨j, rfl⟩ <;>
        simp only [waExt_zero, waExt_last, waExt_mid, Fin.val_zero, Fin.val_last, Fin.val_succ,
          Fin.val_castSucc] <;>
        try simp only [true_and]
      · rw [hxx, if_neg (by omega), if_neg (by omega)]
      · rw [hxy, if_pos (by omega)]
      · have := j.2
        rw [(hmem j).2.1, if_neg (by omega), if_neg (by omega)]
      · rw [hyx, if_pos (by omega)]
      · rw [hyy, if_neg (by omega), if_neg (by omega)]
      · have := j.2
        rw [(hmem j).2.2, if_neg (by omega), if_neg (by omega)]
      · have := i.2
        rw [hbx, if_neg (by omega), if_neg (by omega)]
      · have := i.2
        rw [hby, if_neg (by omega), if_neg (by omega)]
      · have := i.2
        have := j.2
        rw [hgram', wa_witt_apply]
        split_ifs <;> first | rfl | (exfalso; omega)
    · have ht0 : t 0 = 0 := ht 0 (Or.inl (by simp))
      have htl : t (Fin.last (n' + 1)) = 0 := ht _ (Or.inr (by simp only [Fin.val_last]; omega))
      have ht' : (fun j : Fin n' => t (Fin.castSucc j).succ) = 0 := by
        refine hani' _ (fun j hj => ht _ ?_) ?_
        · simp only [Fin.val_succ, Fin.val_castSucc]
          omega
        · rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at hsum
          simpa [ht0, htl, Fin.succ_last] using hsum
      funext i
      rcases wa_cases3 i with rfl | rfl | ⟨j, rfl⟩
      · exact ht0
      · exact htl
      · exact congrFun ht' j
  · have han : ∀ x ∈ W, S.h x x = 0 → x = 0 := fun x hx hxx => by
      by_contra h0
      exact hiso ⟨x, hx, h0, hxx⟩
    obtain ⟨b, hbW, hb0, hbo⟩ := wa_diag S n W hW han
    have hg : ∀ k, S.h (b k) (b k) ≠ 0 := fun k h => hb0 k (han _ (hbW k) h)
    refine ⟨0, b, fun k => S.h (b k) (b k), hbW, by omega, fun i j => ?_, fun t _ hsum => ?_⟩
    · rw [wa_witt_apply]
      have := i.2
      by_cases hij : i = j
      · subst hij
        rw [if_neg (by omega), if_pos ⟨rfl, by omega, by omega⟩]
      · rw [hbo i j hij, if_neg (by omega), if_neg (fun h => hij (Fin.ext h.1))]
    · have hz : ∀ k, S.h (b k) (∑ i, t i • b i) = t k * S.h (b k) (b k) := fun k => by
        rw [wa_sum_right, Finset.sum_eq_single k
          (fun i _ hik => by rw [hbo k i (Ne.symm hik), mul_zero]) (by simp)]
      have hzz : S.h (∑ i, t i • b i) (∑ i, t i • b i) = 0 := by
        rw [wa_sum_left]
        simp only [hz]
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
        beta_reduce
        ring
      have hz0 := han _ (W.sum_mem fun i _ => W.smul_mem _ (hbW i)) hzz
      funext k
      have h := hz k
      rw [hz0, wa_zero_right] at h
      exact (mul_eq_zero.mp h.symm).resolve_right (hg k)
end ReciprocityTheory.MultiplicativeHeights
