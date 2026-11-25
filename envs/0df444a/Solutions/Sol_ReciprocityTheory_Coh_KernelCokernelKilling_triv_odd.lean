-- Prove2me | solution 1 for ReciprocityTheory.Coh.KernelCokernelKilling.triv_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:08.708268+00:00
-- url     : https://prove2.me/submissions/e2913c0d-7fd5-49b3-9e41-26b99cf3f4f3

import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_ShiftA
import Theorems.Thm_ReciprocityTheory_Coh_KernelCokernelKilling_alt_sum_odd
import Theorems.Thm_ReciprocityTheory_Coh_KernelCokernelKilling_dn_triv
import Theorems.Thm_ReciprocityTheory_Coh_Cx_H_ind
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_zero_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_eq_zero_iff



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
open ReciprocityTheory.Coh.KernelCokernelKilling
variable {R : Type u} [CommRing R] {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Subsingleton H]
namespace ReciprocityTheory.Coh.KernelCokernelKilling
theorem _root_.solution (T : TRep R H) (m : ℕ) : Subsingleton (T.H (2 * m + 1)) := by
  refine subsingleton_of_forall_eq 0 fun c => ?_
  induction c using Cx.H_ind with
  | h x hx =>
    rw [Cx.cls_eq_zero_iff]
    have h0 : ∀ g, x.1 g = 0 := fun g => by
      have := congrFun (congrArg Subtype.val hx) (fun _ => 1)
      change dn T.rho (2 * m + 1) x.1 (fun _ => 1) = 0 at this
      rw [dn_triv T.rho (2 * m + 1) _ _ g, alt_sum_odd, one_smul] at this
      exact this
    have : x = 0 := Subtype.ext (funext h0)
    rw [this]
    exact zero_mem _
end ReciprocityTheory.Coh.KernelCokernelKilling
