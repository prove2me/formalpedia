-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.crossOp_khw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:04:19.675732+00:00
-- url     : https://prove2.me/submissions/fa5b7c86-0cb5-4556-9b18-733f9d72cccf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Weights
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_InnerCrossOpEigEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_bAct_isGlRep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimirK_bAct
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimirK_irr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimirK_mAct_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_factorCasimir_ncV_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_khw_big_weight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ncV_mem

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
section One
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
private theorem casimirK_eq_casValK_smul_of_isKHWVec {X : Type*} [AddCommGroup X] [Module ℂ X]
    {A : Fin n → Fin n → Module.End ℂ X} (hA : IsGlRep A) {μ : Fin n → ℝ} {w : X}
    (hw : IsKHWVec ε A μ w) : casimirK ε A w = (casValK ε μ : ℂ) • w := by
  have hA' : ∀ a b c d : Fin n, A a b * A c d - A c d * A a b =
      (if b = c then A a d else 0) - (if d = a then A c b else 0) := hA
  have term : ∀ a b : Fin n, ε b = ε a → A a b (A b a w) =
      ((((if b = a then μ a ^ 2 else 0) + (if a < b then μ a - μ b else 0) : ℝ)) : ℂ) • w := by
    intro a b hab
    rcases lt_trichotomy b a with h | h | h
    · rw [hw.2 b a h hab, map_zero, if_neg (ne_of_lt h), if_neg (lt_asymm h)]
      simp
    · subst h
      rw [if_pos rfl, if_neg (lt_irrefl b), add_zero, hw.1 b, map_smul, hw.1 b, smul_smul,
        ← Complex.ofReal_mul, ← sq]
    · have e := LinearMap.congr_fun (hA' a b b a) w
      simp only [LinearMap.sub_apply, Module.End.mul_apply, eq_self_iff_true, if_true,
        hw.2 a b h hab.symm, map_zero, sub_zero] at e
      rw [e, if_neg (ne_of_gt h), if_pos h, hw.1 a, hw.1 b]
      simp [sub_smul]
  have hsum : casimirK ε A w = ((∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
      ((if b = a then μ a ^ 2 else 0) + (if a < b then μ a - μ b else 0)) : ℝ) : ℂ) • w := by
    simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply, Complex.ofReal_sum,
      Finset.sum_smul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb =>
      term a b (Finset.mem_filter.mp hb).2
  have hA2 : ∀ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
      ((if b = a then μ a ^ 2 else 0) + (if a < b then μ a - μ b else 0)) =
      μ a ^ 2 + ((∑ b, if a < b ∧ ε b = ε a then μ a else 0) -
        ∑ b, if a < b ∧ ε b = ε a then μ b else 0) := by
    intro a
    rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
    have h2 : μ a ^ 2 = ∑ b, (if b = a then μ a ^ 2 else 0) := by simp
    conv_rhs => rw [h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp_all
  have hC : (∑ a, ∑ b, if a < b ∧ ε b = ε a then μ b else 0) =
      ∑ a, ∑ b, if b < a ∧ ε b = ε a then μ a else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h1 : b < a ∧ ε a = ε b
    · rw [if_pos h1, if_pos ⟨h1.1, h1.2.symm⟩]
    · rw [if_neg h1, if_neg fun h2 => h1 ⟨h2.1, h2.2.symm⟩]
  have hρ : ∀ a, 2 * rhoC ε a = (∑ b, if a < b ∧ ε b = ε a then (1 : ℝ) else 0) -
      ∑ b, if b < a ∧ ε b = ε a then (1 : ℝ) else 0 := by
    intro a
    simp only [rhoC]
    rw [Finset.sum_boole, Finset.sum_boole]
    ring
  have hR : casValK ε μ = ∑ a, (μ a ^ 2 + μ a * (2 * rhoC ε a)) := by
    simp only [casValK, nsq, dot, Pi.add_apply]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hsum, hR, Finset.sum_congr rfl fun a _ => hA2 a]
  congr 2
  simp only [hρ, mul_sub, Finset.mul_sum, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hC]
end One
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
theorem _root_.solution (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) {x : Big n 1 M} (hx : x ∈ ncV ε V 1) (hx0 : x ≠ 0)
    {ν : Fin n → ℝ} (hν : IsKHWVec ε (bAct E 1) ν x) :
    ∃ r s : Fin n, ε r ≠ ε s ∧ ν = lowK ε lam + root r s ∧
      (2 : ℂ) • crossOp ε E 1 0 x =
        ((casValK ε ν - n - casValK ε (lowK ε lam) : ℝ) : ℂ) • x := by
  obtain ⟨γ, hγ, hνγ⟩ := khw_big_weight hE hV hx hx0 hν
  refine ⟨(γ 0).1, (γ 0).2, hγ 0, ?_, ?_⟩
  · rw [Fin.sum_univ_one] at hνγ
    rw [← hνγ]
    abel
  · have hm : casimirK ε (mAct E 1) x = (casValK ε (lowK ε lam) : ℂ) • x := by
      ext κ
      rw [casimirK_mAct_apply, casimirK_irr hE hV _ (ncV_mem hx κ)]
      rfl
    have hcas := LinearMap.congr_fun (casimirK_bAct (ε := ε) (E := E) 1) x
    rw [casimirK_eq_casValK_smul_of_isKHWVec (bAct_isGlRep hE 1) hν] at hcas
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Fin.sum_univ_one, factorCasimir_ncV_one hx,
      hm, two_smul] at hcas
    rw [two_smul]
    push_cast
    rw [sub_smul, sub_smul, hcas]
    abel
end ReciprocityTheory.ChartRestriction.DS
