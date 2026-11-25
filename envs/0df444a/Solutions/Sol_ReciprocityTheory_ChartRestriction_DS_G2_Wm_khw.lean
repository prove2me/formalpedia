-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.G2.Wm_khw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:38:11.237201+00:00
-- url     : https://prove2.me/submissions/1981002d-4ebc-4426-aad4-a631a9843535

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_StdGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_BochnerG2_CrossOpEigGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_BochnerG2_Numerics
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_BochnerG2_NcVOneDecomp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Wm_perp_Wp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_crossOp_khw

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
namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}
section OneB
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
private lemma nsq_add_root_sub_nsq (w : Fin n → ℝ) {r s : Fin n} (hrs : r ≠ s) :
    nsq (w + root r s) - nsq w = 2 * (w r - w s) + 2 := by
  have key : ∀ i, (w + root r s) i * (w + root r s) i - w i * w i =
      (if i = r then 2 * w r + 1 else 0) + (if i = s then -(2 * w s) + 1 else 0) := by
    intro i
    simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    by_cases h1 : i = r
    · subst h1
      simp [hrs]
      ring
    · by_cases h2 : i = s
      · subst h2
        simp [h1]
        ring
      · simp [h1, h2]
  unfold nsq dot
  rw [← Finset.sum_sub_distrib]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring
private lemma abs_rhoN_le_half (ε : Fin n → Bool) (a : Fin n) :
    -(n : ℝ) / 2 ≤ rhoN ε a ∧ rhoN ε a ≤ (n : ℝ) / 2 := by
  have key : ∀ t : Finset (Fin n), (t.card : ℝ) ≤ n := fun t => by
    have := Finset.card_le_univ t
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  simp only [rhoN]
  constructor
  · linarith [key (Finset.filter (fun b => b < a ∧ ε b ≠ ε a) Finset.univ),
      (Nat.cast_nonneg (Finset.filter (fun b => a < b ∧ ε b ≠ ε a) Finset.univ).card : (0 : ℝ) ≤ _)]
  · linarith [key (Finset.filter (fun b => a < b ∧ ε b ≠ ε a) Finset.univ),
      (Nat.cast_nonneg (Finset.filter (fun b => b < a ∧ ε b ≠ ε a) Finset.univ).card : (0 : ℝ) ≤ _)]
end OneB
end ReciprocityTheory.ChartRestriction.DS.G2
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.G2
theorem _root_.solution (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {x : Big n 1 M} (hx : x ∈ Wm ε E V) (hx0 : x ≠ 0) {ν : Fin n → ℝ}
    (hν : IsKHWVec ε (bAct E 1) ν x) :
    ∃ a b : Fin n, a < b ∧ ε a ≠ ε b ∧ ν = lowK ε lam - root a b := by
  have hle : Wm ε E V ≤ ncV ε V 1 := by
    show (⨆ (θ : ℝ) (_ : θ < 0),
      Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1) ≤ ncV ε V 1
    exact iSup₂_le fun θ _ => inf_le_right
  have hxN : x ∈ ncV ε V 1 := hle hx
  obtain ⟨r, s, hrs, hν', hC⟩ := crossOp_khw hE hU hV hxN hx0 hν
  have hne : r ≠ s := fun h' => hrs (h' ▸ rfl)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exfalso
    have hdiff : casValK ε ν - casValK ε (lowK ε lam) =
        2 * ((lowK ε lam + rhoC ε) r - (lowK ε lam + rhoC ε) s) + 2 := by
      rw [hν']
      unfold casValK
      rw [add_right_comm]
      linarith [nsq_add_root_sub_nsq (lowK ε lam + rhoC ε) hne]
    have hw : ∀ i, (lowK ε lam + rhoC ε) i = lam i + rhoN ε i := by
      intro i
      simp [lowK]
    have hgap : h ≤ lam r - lam s := by
      have h1 := hh r s hrs
      rwa [abs_of_pos (sub_pos.2 (hmono hlt))] at h1
    have hcpos : 0 < (casValK ε ν - n - casValK ε (lowK ε lam)) / 2 := by
      rw [hw r, hw s] at hdiff
      linarith [(abs_rhoN_le_half ε r).1, (abs_rhoN_le_half ε s).2]
    have heig : crossOp ε E 1 0 x =
        (((casValK ε ν - n - casValK ε (lowK ε lam)) / 2 : ℝ) : ℂ) • x := by
      have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
      calc crossOp ε E 1 0 x = (2 : ℂ)⁻¹ • ((2 : ℂ) • crossOp ε E 1 0 x) := by
            rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
        _ = (2 : ℂ)⁻¹ • (((casValK ε ν - n - casValK ε (lowK ε lam) : ℝ) : ℂ) • x) := by
            rw [hC]
        _ = _ := by
            rw [smul_smul]
            congr 1
            push_cast
            ring
    have hxP : x ∈ Wp ε E V := by
      show x ∈ ⨆ (θ : ℝ) (_ : 0 < θ),
        Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1
      exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hcpos
        (Submodule.mem_inf.2 ⟨Module.End.mem_eigenspace_iff.2 heig, hxN⟩))
    exact hx0 (inner_self_eq_zero.1 (Wm_perp_Wp hU hx hxP))
  · refine ⟨s, r, hgt, fun h' => hrs h'.symm, ?_⟩
    rw [hν']
    unfold root
    abel
end ReciprocityTheory.ChartRestriction.DS.G2
