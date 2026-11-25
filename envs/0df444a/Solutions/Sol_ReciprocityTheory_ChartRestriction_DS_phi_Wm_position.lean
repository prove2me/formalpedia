-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.phi_Wm_position
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:54:56.976707+00:00
-- url     : https://prove2.me/submissions/5e25bebb-1802-4196-9a69-cfc436b6a22e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PhiPerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SchPhiOneApply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sch_slice_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sch_permute_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_phi_Wm_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_phi_permute_sub_mem


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
theorem _root_.solution (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {k : ℕ} (i : Fin (k + 1)) {F : Big n (k + 1) M} (hF0 : F ∈ ncV ε V (k + 1))
    (hF : ∀ κ, slice i κ F ∈ Wm ε E V) : phi E (k + 1) F ∈ layer ε E V k := by

  have hperm : ∀ κ, slice (Fin.last k) κ (permute (Equiv.swap i (Fin.last k)) F) ∈ Wm ε E V := by
    intro κ
    have heq : slice (Fin.last k) κ (permute (Equiv.swap i (Fin.last k)) F) =
        slice i (κ ∘ Equiv.swap i (Fin.last k)) F := by
      refine PiLp.ext fun ι => ?_
      rw [sch_slice_apply, sch_permute_apply, sch_slice_apply, Function.update_comp_equiv,
        Equiv.symm_swap, Equiv.swap_apply_right]
    rw [heq]
    exact hF _
  have h0 := phi_Wm_last hE hU hV hc hmono hh hbig hperm
  have hsub := phi_permute_sub_mem hE hV.2.1 (Equiv.swap i (Fin.last k)) hF0
  rw [h0, sub_zero] at hsub
  exact hsub
end ReciprocityTheory.ChartRestriction.DS
