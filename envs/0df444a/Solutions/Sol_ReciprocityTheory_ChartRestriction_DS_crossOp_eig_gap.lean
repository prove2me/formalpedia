-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.crossOp_eig_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:12:34.261571+00:00
-- url     : https://prove2.me/submissions/e70d03f2-e43a-463a-9d9d-64f505dcbf35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_InnerCrossOpEigEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CrossOpEigGap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_factorAd_mem_ncV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_mAct_mem_ncV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_bAct_isGlRep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_bAct_isKUnitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimirK_mem_of_kStable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_crossOp_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_crossOp_khw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_eig_casimirK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_finiteDimensional_ncV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section OneBAux
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
private lemma card_opposite_sign_above_add_below_le (e : Fin n → Bool) (a : Fin n) :
    ((univ.filter fun b => a < b ∧ e b ≠ e a).card : ℝ) +
      ((univ.filter fun b => b < a ∧ e b ≠ e a).card : ℝ) ≤
      ((univ.filter fun b => e b ≠ e a).card : ℝ) := by
  have hd : Disjoint (univ.filter fun b => a < b ∧ e b ≠ e a)
      (univ.filter fun b => b < a ∧ e b ≠ e a) := by
    rw [Finset.disjoint_filter]
    intro b _ h1 h2
    exact lt_asymm h1.1 h2.1
  rw [← Nat.cast_add, ← Finset.card_union_of_disjoint hd]
  exact_mod_cast Finset.card_le_card (fun b hb => by
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rcases hb with h | h
    · exact h.2
    · exact h.2)
private lemma card_opposite_sign_add_le_of_ne (e : Fin n → Bool) {r s : Fin n} (hrs : e r ≠ e s) :
    ((univ.filter fun b => e b ≠ e r).card : ℝ) + ((univ.filter fun b => e b ≠ e s).card : ℝ) ≤ n := by
  have key : ∀ x y z : Bool, x ≠ y → x ≠ z → y ≠ z → False := by decide
  have hd : Disjoint (univ.filter fun b => e b ≠ e r) (univ.filter fun b => e b ≠ e s) := by
    rw [Finset.disjoint_filter]
    intro b _ h1 h2
    exact key _ _ _ h1 h2 hrs
  rw [← Nat.cast_add, ← Finset.card_union_of_disjoint hd]
  exact_mod_cast (Finset.card_le_univ _).trans (by simp)
end OneBAux
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {θ : ℝ} {y : Big n 1 M}
    (hy : y ∈ Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1) (hy0 : y ≠ 0) :
    (0 < h - n + 1 ∧ h - n + 1 ≤ θ) ∨ (θ ≤ -h - 1 ∧ -h - 1 < 0) := by
  classical
  have hVfd : FiniteDimensional ℂ V := hV.1
  haveI := finiteDimensional_ncV (ε := ε) hVfd 1
  set S := Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1 with hSdef
  haveI hfd : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le inf_le_right

  have hSst : IsKStableSub ε (bAct E 1) S := by
    intro a b hab v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff] at hv1 ⊢
      have hc := congrArg (fun T : Module.End ℂ (Big n 1 M) => T v) (crossOp_comm hE 1 0 hab)
      simp only [Module.End.mul_apply] at hc
      rw [hc, hv1, map_smul]
    · simp only [bAct, LinearMap.add_apply, LinearMap.sum_apply]
      exact Submodule.add_mem _ (BigCasimir.mAct_mem_ncV hV.2.1 1 hab hv2)
        (Submodule.sum_mem _ fun i _ => BigCasimir.factorAd_mem_ncV i hab hv2)

  have hCS : ∀ x ∈ S, casimirK ε (bAct E 1) x ∈ S := fun x hx => casimirK_mem_of_kStable hSst hx
  let T : Module.End ℂ S := (casimirK ε (bAct E 1)).restrict hCS
  haveI : Nontrivial S := ⟨⟨⟨y, hy⟩, 0, fun h => hy0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hvT := Module.End.mem_eigenspace_iff.1 hv.1
  have hx0 : (v : Big n 1 M) ≠ 0 := fun h => hv.2 (Subtype.ext h)
  have hxθ : casimirK ε (bAct E 1) (v : Big n 1 M) = c • (v : Big n 1 M) := congrArg Subtype.val hvT
  obtain ⟨w, hwS, hw0, -, μ, hμw, -⟩ :=
    eig_casimirK (bAct_isGlRep hE 1) (bAct_isKUnitary hU 1) hfd hSst v.2 hx0 hxθ
  obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.1 hwS
  obtain ⟨r, s, hε, hμ, hcross⟩ := crossOp_khw hE hU hV hw2 hw0 hμw
  have hθw : crossOp ε E 1 0 w = (θ : ℂ) • w := Module.End.mem_eigenspace_iff.1 hw1
  rw [hθw, smul_smul] at hcross
  have h2 := smul_left_injective ℂ hw0 hcross
  have h2θ : 2 * θ = casValK ε μ - n - casValK ε (lowK ε lam) := by
    have h3 : ((2 * θ : ℝ) : ℂ) = ((casValK ε μ - n - casValK ε (lowK ε lam) : ℝ) : ℂ) := by
      rw [← h2]
      push_cast
      ring
    exact_mod_cast h3

  have hrs : r ≠ s := fun h => hε (congrArg ε h)
  have hroot : ∀ u : Fin n → ℝ, nsq (u + root r s) - nsq u = 2 * (u r - u s) + 2 := by
    intro u
    have hs : ∀ a, root r s a = (if a = r then (1 : ℝ) else 0) - (if a = s then 1 else 0) := fun a => by
      simp [root, Pi.single_apply]
    simp only [nsq, dot, Pi.add_apply, hs]
    rw [← Finset.sum_sub_distrib]
    have e : ∀ a, (u a + ((if a = r then (1 : ℝ) else 0) - (if a = s then 1 else 0))) *
        (u a + ((if a = r then (1 : ℝ) else 0) - (if a = s then 1 else 0))) - u a * u a =
        2 * (if a = r then u a else 0) - 2 * (if a = s then u a else 0) +
          (if a = r then (1 : ℝ) else 0) + (if a = s then (1 : ℝ) else 0) := fun a => by
      split_ifs with h1 h2 h2
      · exact absurd (h1.symm.trans h2) hrs
      all_goals ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hcas : casValK ε μ - casValK ε (lowK ε lam) =
      2 * ((lowK ε lam + rhoC ε) r - (lowK ε lam + rhoC ε) s) + 2 := by
    rw [hμ]
    unfold casValK
    rw [show lowK ε lam + root r s + rhoC ε = (lowK ε lam + rhoC ε) + root r s by abel]
    linarith [hroot (lowK ε lam + rhoC ε)]
  have hL : ∀ a, (lowK ε lam + rhoC ε) a = lam a + rhoN ε a := fun a => by simp [lowK]
  rw [hL r, hL s] at hcas
  have hθ : θ = (lam r + rhoN ε r) - (lam s + rhoN ε s) + 1 - n / 2 := by linarith

  have hrN : ∀ a, rhoN ε a = (((univ.filter fun b => a < b ∧ ε b ≠ ε a).card : ℝ) -
      ((univ.filter fun b => b < a ∧ ε b ≠ ε a).card : ℝ)) / 2 := fun a => rfl
  have hPr := card_opposite_sign_above_add_below_le ε r
  have hPs := card_opposite_sign_above_add_below_le ε s
  have hO := card_opposite_sign_add_le_of_ne ε hε
  have hpq : 1 ≤ (pOf ε : ℝ) ∧ 1 ≤ (qOf ε : ℝ) := by
    have key : ∀ x y c : Bool, x ≠ y → x ≠ c → y = c := by decide
    have hmem : ∀ c : Bool, ∃ a, ε a = c := fun c => by
      by_cases h1 : ε r = c
      · exact ⟨r, h1⟩
      · exact ⟨s, key _ _ _ hε h1⟩
    unfold pOf qOf
    obtain ⟨a1, ha1⟩ := hmem true
    obtain ⟨a2, ha2⟩ := hmem false
    exact ⟨Nat.one_le_cast.2 (Finset.card_pos.2 ⟨a1, by simp [ha1]⟩),
      Nat.one_le_cast.2 (Finset.card_pos.2 ⟨a2, by simp [ha2]⟩)⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpq1 : (1 : ℝ) * 1 ≤ (pOf ε : ℝ) * (qOf ε : ℝ) :=
    mul_le_mul hpq.1 hpq.2 zero_le_one (by linarith [hpq.1])
  have hnpq : (n : ℝ) * 1 ≤ (n : ℝ) * ((pOf ε : ℝ) * (qOf ε : ℝ)) := by
    rw [one_mul] at hpq1
    exact mul_le_mul_of_nonneg_left hpq1 hn0
  have hhn : (n : ℝ) + 1 < h := by nlinarith
  rcases le_abs'.1 (hh r s hε) with hcase | hcase
  ·
    have hlt : s < r := not_le.1 fun hle => absurd (hmono.antitone hle) (not_le.2 (by linarith))
    have h1 : (1 : ℝ) ≤ ((univ.filter fun b => s < b ∧ ε b ≠ ε s).card : ℝ) :=
      Nat.one_le_cast.2 (Finset.card_pos.2 ⟨r, by simp [hlt, hε]⟩)
    have h2' : (1 : ℝ) ≤ ((univ.filter fun b => b < r ∧ ε b ≠ ε r).card : ℝ) :=
      Nat.one_le_cast.2 (Finset.card_pos.2 ⟨s, by simp [hlt, Ne.symm hε]⟩)
    right
    refine ⟨?_, by linarith⟩
    rw [hθ, hrN r, hrN s]
    linarith
  ·
    have hlt : r < s := not_le.1 fun hle => absurd (hmono.antitone hle) (not_le.2 (by linarith))
    have h1 : (1 : ℝ) ≤ ((univ.filter fun b => r < b ∧ ε b ≠ ε r).card : ℝ) :=
      Nat.one_le_cast.2 (Finset.card_pos.2 ⟨s, by simp [hlt, Ne.symm hε]⟩)
    have h2' : (1 : ℝ) ≤ ((univ.filter fun b => b < s ∧ ε b ≠ ε s).card : ℝ) :=
      Nat.one_le_cast.2 (Finset.card_pos.2 ⟨r, by simp [hlt, hε]⟩)
    left
    refine ⟨by linarith, ?_⟩
    rw [hθ, hrN r, hrN s]
    linarith
end ReciprocityTheory.ChartRestriction.DS
