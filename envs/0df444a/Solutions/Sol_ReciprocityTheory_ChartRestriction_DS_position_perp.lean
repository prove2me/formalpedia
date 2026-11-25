-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.position_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:31:58.560923+00:00
-- url     : https://prove2.me/submissions/ef070382-6569-4e91-b6d0-ca2452c3d3be

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SltEqZeroOfCompact
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CrossOpSlotBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Wm_le_ncV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Wm_perp_Wp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ncV_one_decomp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slice_eq_slt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slt_inner_eq_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slt_mem_ncV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slt_mem_ncV_iff


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
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {k : ℕ} (i : Fin k) {P : Big n k M} (hP : P ∈ ncV ε V k)
    (hperp : ∀ F ∈ ncV ε V k, (∀ κ, slice i κ F ∈ Wm ε E V) → inner ℂ F P = 0) :
    ∀ κ, slice i κ P ∈ Wp ε E V := by
  intro κ
  rw [slice_eq_slt]
  set r := (slRest i κ).2 with hr
  have hx : slt i r P ∈ ncV ε V 1 := slt_mem_ncV i r hP
  obtain ⟨xm, hxm, xp, hxp, hdec⟩ := ncV_one_decomp hE hU hV hmono hh hbig hx
  have hkey : inner ℂ xm (slt i r P) = (‖xm‖ : ℂ) ^ 2 := by
    rw [hdec, inner_add_right, Wm_perp_Wp hU hxm hxp, add_zero]
    exact inner_self_eq_norm_sq_to_K xm
  suffices hz : xm = 0 by
    rw [hdec, hz, zero_add]
    exact hxp
  have hxm1 := slt_mem_ncV_iff.1 (Wm_le_ncV hxm)

  have hbad : (∃ j : {j // j ≠ i}, ε (r j).1 = ε (r j).2) → xm = 0 := by
    rintro ⟨j, hj⟩
    have hx0 : slt i r P = 0 := by
      ext ι
      have hPm := (slt_mem_ncV_iff.1 hP) ((slRest i).symm (ι 0, r))
      have hcoord : ((slRest i).symm (ι 0, r)) j.1 = r j := by
        simp [slRest, Equiv.funSplitAt_symm_apply, j.2]
      rw [if_neg] at hPm
      · simpa [slt] using hPm
      · intro hall
        exact hall j.1 (by rw [hcoord]; exact hj)
    have h2 := hkey
    rw [hx0, inner_zero_right] at h2
    simpa using h2.symm
  let F : Big n k M := WithLp.toLp 2 (fun κ' =>
    if (slRest i κ').2 = r then xm (fun _ => (slRest i κ').1) else 0)
  have hFapp : ∀ κ', F κ' = if (slRest i κ').2 = r then xm (fun _ => (slRest i κ').1) else 0 :=
    fun κ' => rfl
  have hsltF : ∀ r', slt i r' F = if r' = r then xm else 0 := by
    intro r'
    split_ifs with h1
    · subst h1
      ext ι
      simp only [slt, hFapp]
      simp only [Equiv.apply_symm_apply, if_true]
      rw [show (fun _ : Fin 1 => ι 0) = ι from funext fun j => by rw [Fin.fin_one_eq_zero j]]
    · ext ι
      simp [slt, hFapp, h1]
  have hFmem : F ∈ ncV ε V k := by
    rw [slt_mem_ncV_iff]
    intro κ'
    rw [hFapp]
    by_cases hrest : (slRest i κ').2 = r
    · rw [if_pos hrest]
      have hι := hxm1 (fun _ => (slRest i κ').1)
      by_cases hc : ∀ j, ε (κ' j).1 ≠ ε (κ' j).2
      · rw [if_pos hc]
        split_ifs at hι
        · exact hι
        · rw [(Submodule.mem_bot ℂ).1 hι]
          exact zero_mem _
      · rw [if_neg hc]
        push_neg at hc
        obtain ⟨j, hj⟩ := hc
        by_cases hji : j = i
        · subst hji
          rw [if_neg] at hι
          · exact hι
          · intro hall
            exact hall 0 (by simpa [slRest] using hj)
        · rw [hbad ⟨⟨j, hji⟩, by rw [← hrest]; simpa [slRest] using hj⟩]
          simp
    · rw [if_neg hrest]
      exact zero_mem _
  have hinner : inner ℂ F P = inner ℂ xm (slt i r P) := by
    rw [slt_inner_eq_sum i F P]
    simp only [hsltF]
    rw [Finset.sum_eq_single r (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have hF0 := hperp F hFmem (fun κ' => by
    rw [slice_eq_slt, hsltF]
    split_ifs
    · exact hxm
    · exact zero_mem _)
  rw [hinner, hkey] at hF0
  simpa using hF0
end ReciprocityTheory.ChartRestriction.DS
