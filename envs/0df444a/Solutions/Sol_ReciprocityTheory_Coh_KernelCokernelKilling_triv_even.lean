-- Prove2me | solution 1 for ReciprocityTheory.Coh.KernelCokernelKilling.triv_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:05.202138+00:00
-- url     : https://prove2.me/submissions/5e18989c-98d2-4e44-9c80-40ed78902ad9

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
theorem _root_.solution (T : TRep R H) (m : ℕ) : Subsingleton (T.H (2 * m + 1 + 1)) := by
  refine subsingleton_of_forall_eq 0 fun c => ?_
  induction c using Cx.H_ind with
  | h x hx =>
    rw [Cx.cls_eq_zero_iff]
    refine ⟨⟨fun _ => x.1 fun _ => 1, continuous_const⟩, Subtype.ext (funext fun g => ?_)⟩
    show dn T.rho (2 * m + 1) (fun _ => x.1 fun _ => 1) g = x.1 g
    rw [dn_triv T.rho (2 * m + 1) _ g (fun _ => 1), alt_sum_odd, one_smul,
      Subsingleton.elim g (fun _ => 1)]
end ReciprocityTheory.Coh.KernelCokernelKilling
