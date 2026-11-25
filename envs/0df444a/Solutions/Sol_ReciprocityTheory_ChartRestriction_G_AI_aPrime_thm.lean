-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.aPrime_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:35:46.265474+00:00
-- url     : https://prove2.me/submissions/12879ffe-f388-488d-b19d-439604136f96

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_APrime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_cons_cons_word
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_symm_consWord_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_symm_consWord_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution : APrimeStatement := by
  intro D S k hk hkD
  have hstep : ∀ i ∈ Finset.range k,
      S.Φ (word D k i (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A)) =
        S.IW (fun j => interp k (i + 1) (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j) -
          S.IW (fun j => interp k i (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [← S.diag, cons_cons_word D k i hk, cons_cons_word D k i hk,
      symm_consWord_left S.IW S.symmW k i hi hkD,
      symm_consWord_right S.IW S.symmW k i hi hkD]
  have hsum : ∑ i ∈ Finset.range k, S.Φ (word D k i (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A)) =
      S.IW (fun j => interp k k (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j) -
        S.IW (fun j => interp k 0 (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j) := by
    rw [Finset.sum_congr rfl hstep]
    exact Finset.sum_range_sub
      (fun m => S.IW (fun j => interp k m (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j)) k
  have hzero : S.IW (fun j => interp k 0 (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j) = 0 := by
    have h := S.comp_right_eq_zero_alt
      (fun j : Fin (D + 2) => if (j : ℕ) < 1 + 2 * k then S.ξ else S.A)
    refine Eq.trans ?_ h
    congr 1
    funext j
    simp only [interp]
    split_ifs <;> first | rfl | exact S.base | omega
  have hfun : (Fin.cons (S.p₂ S.ξ) (fun j => S.p₁ (mix (2 * k) S.ξ S.A j)) :
      Fin (D + 2) → S.VW) =
      fun j : Fin (D + 2) => interp k k (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) (j : ℕ) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [interp]
    · rw [Fin.cons_succ, Fin.val_succ]
      show S.p₁ (if (j : ℕ) < 2 * k then S.ξ else S.A) =
        (if (j : ℕ) + 1 = 0 then S.p₂ S.ξ else if (j : ℕ) + 1 < 1 + 2 * k then S.p₁ S.ξ else
          if (j : ℕ) + 1 < 1 + 2 * k then S.p₂ S.ξ else S.p₁ S.A)
      have h0 : ¬((j : ℕ) + 1 = 0) := by omega
      by_cases h : (j : ℕ) < 2 * k
      · have h1 : (j : ℕ) + 1 < 1 + 2 * k := by omega
        rw [if_pos h, if_neg h0, if_pos h1]
      · have h1 : ¬((j : ℕ) + 1 < 1 + 2 * k) := by omega
        rw [if_neg h, if_neg h0, if_neg h1, if_neg h1]
  have htop : S.I (mix (2 * k) S.ξ S.A) =
      -S.IW (fun j => interp k k (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j) := by
    rw [← S.cons_comp_left, show -(S.p₂ S.ξ) = (-1 : ℝ) • S.p₂ S.ξ by simp,
      MultilinearMap.cons_smul, neg_one_smul, hfun]
  rw [hsum, hzero, htop, sub_zero]
end ReciprocityTheory.ChartRestriction.G.AI
