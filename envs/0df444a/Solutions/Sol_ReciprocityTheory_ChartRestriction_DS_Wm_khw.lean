-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Wm_khw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:24:51.886478+00:00
-- url     : https://prove2.me/submissions/81ee581b-6fb9-435d-84e6-797d1b60e8c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CrossOpEigGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Wm_le_ncV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_crossOp_khw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_crossVal_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gap_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_inner_crossOp_eig_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {x : Big n 1 M} (hx : x ∈ Wm ε E V) (hx0 : x ≠ 0) {ν : Fin n → ℝ}
    (hν : IsKHWVec ε (bAct E 1) ν x) :
    ∃ a b : Fin n, a < b ∧ ε a ≠ ε b ∧ ν = lowK ε lam - root a b := by
  have hxN := Wm_le_ncV hx
  obtain ⟨r, s, hrs, hν', hC2⟩ := crossOp_khw hE hU hV hxN hx0 hν
  have hne : r ≠ s := fun h => hrs (h ▸ rfl)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exfalso
    have hgap := (gap_gt hrs hbig).2
    have hcpos := crossVal_pos hmono hh hlt hrs
    rw [← hν'] at hcpos
    have hCx : crossOp ε E 1 0 x =
        (((casValK ε ν - n - casValK ε (lowK ε lam)) / 2 : ℝ) : ℂ) • x := by
      calc crossOp ε E 1 0 x = (1 / 2 : ℂ) • ((2 : ℂ) • crossOp ε E 1 0 x) := by
            rw [smul_smul]; norm_num
        _ = _ := by rw [hC2, smul_smul]; congr 1; push_cast; ring
    have horth : ∀ y ∈ Wm ε E V, inner ℂ y x = 0 := by
      intro y hy
      unfold Wm at hy
      refine Submodule.iSup_induction _ (motive := fun y => inner ℂ y x = 0) hy ?_ (inner_zero_left _)
        (fun a b ha hb => by rw [inner_add_left, ha, hb, add_zero])
      intro θ y hy
      refine Submodule.iSup_induction _ (motive := fun y => inner ℂ y x = 0) hy ?_ (inner_zero_left _)
        (fun a b ha hb => by rw [inner_add_left, ha, hb, add_zero])
      intro hθ y hy
      exact inner_crossOp_eig_eq_zero hU (ne_of_lt (by linarith)) (Module.End.mem_eigenspace_iff.1 hy.1) hCx
    exact hx0 (inner_self_eq_zero.1 (horth x hx))
  · refine ⟨s, r, hlt, fun h => hrs h.symm, ?_⟩
    rw [hν']
    unfold root
    abel
end ReciprocityTheory.ChartRestriction.DS
