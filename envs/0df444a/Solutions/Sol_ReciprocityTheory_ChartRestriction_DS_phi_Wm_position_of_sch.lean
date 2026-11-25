-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.phi_Wm_position_of_sch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:56:41.156225+00:00
-- url     : https://prove2.me/submissions/4709a61b-0e24-4d79-8c73-1a16a104ec7f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SchForm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_phi_Wm_last_of_sch
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_big_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_big_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_phi_permute_sub_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sch_permute_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sch_slice_apply


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
theorem _root_.solution (hE : IsGlRep E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hSch : ∀ x ∈ Wm ε E V, phi E 1 x = 0) {k : ℕ} (i : Fin (k + 1)) {F : Big n (k + 1) M}
    (hF0 : F ∈ ncV ε V (k + 1)) (hF : ∀ κ, slice i κ F ∈ Wm ε E V) :
    phi E (k + 1) F ∈ layer ε E V k := by
  have hsub := phi_permute_sub_mem hE hV.2.1 (Equiv.swap i (Fin.last k)) hF0
  have hzero : phi E (k + 1) (permute (Equiv.swap i (Fin.last k)) F) = 0 := by
    apply phi_Wm_last_of_sch hSch
    intro κ
    have hs : slice (Fin.last k) κ (permute (Equiv.swap i (Fin.last k)) F) =
        slice i (κ ∘ Equiv.swap i (Fin.last k)) F := by
      apply big_ext
      intro ι
      rw [sch_slice_apply, sch_slice_apply, sch_permute_apply, Function.update_comp_equiv,
        Equiv.symm_swap, Equiv.swap_apply_right]
    rw [hs]
    exact hF _
  rw [hzero, sub_zero] at hsub
  exact hsub
end ReciprocityTheory.ChartRestriction.DS
