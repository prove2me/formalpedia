-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTransgression.cls_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:47.839243+00:00
-- url     : https://prove2.me/submissions/156d92e2-b545-49e2-9e43-3d0793021551

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionA
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionB
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_hom_f_injective
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_inflation_hom_degree_one_apply
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_inflD_of_d
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_descend1
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_iff
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_mem_oneCoboundaries_iff
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_oneCochain_apply_fin_one
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_zeroDifferential_val
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_inflD_of_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationTransgression
open ReciprocityTheory.Gal ReciprocityTheory.Coh Cx Function InflationRestrictionInvariants
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)
  (hP : IsInvRep M N Q P)
include hP
namespace ReciprocityTheory.Coh.InflationTransgression
theorem _root_.solution (y y' : M.coch.X 1) (z z' : Q.coch.X 2) (hz : Q.coch.d 2 z = 0)
    (hz' : Q.coch.d 2 z' = 0) (hd : M.coch.d 1 y = P.hom.f 2 z) (hd' : M.coch.d 1 y' = P.hom.f 2 z')
    (hr : (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (y - y') ∈ (M.resSub N).coch.B 1) :
    Q.coch.cls 2 z hz = Q.coch.cls 2 z' hz' := by
  obtain ⟨m, hm⟩ : ∃ m : M.V, ∀ n : N, y.1 (e1 (n : G)) - y'.1 (e1 (n : G)) = M.rho n m - m :=
    (mem_oneCoboundaries_iff _ _).1 hr
  obtain ⟨w, hw⟩ : ∃ w : M.coch.X 1, w = y - y' - M.coch.d 0 (const0 M m) := ⟨_, rfl⟩
  have hwv : ∀ a, w.1 (e1 a) = y.1 (e1 a) - y'.1 (e1 a) - (M.rho a m - m) := fun a => by
    rw [hw]
    show y.1 (e1 a) - y'.1 (e1 a) - (M.coch.d 0 (const0 M m)).1 (e1 a) = _
    rw [zeroDifferential_val]; rfl
  have hwN : ∀ n : N, w.1 (e1 n) = 0 := fun n => by
    rw [hwv, hm n, sub_self]
  have hdw : M.coch.d 1 w = P.hom.f 2 (z - z') := by
    rw [hw, map_sub, map_sub, M.coch.dd, sub_zero, hd, hd', map_sub]
  have hI := inflD_of_d M N Q P hP w (z - z') hdw
  have h1 : (fun g => w.1 (e1 g)) 1 = 0 := by
    have e := hwN 1
    rwa [OneMemClass.coe_one] at e
  obtain ⟨hr1, hr2⟩ := inflD_of_zero M N (fun g => w.1 (e1 g)) h1 hI hwN
  obtain ⟨v, hv⟩ := descend1 M N Q P hP (fun g => w.1 (e1 g))
    ((show Continuous w.1 from w.2).comp (continuous_pi fun _ => continuous_id)) hr1 hr2
  have hvw : P.hom.f 1 v = w := Subtype.ext (funext fun g => by
    rw [oneCochain_apply_fin_one M _ g, oneCochain_apply_fin_one M w g, inflation_hom_degree_one_apply M N Q P hP, hv])
  have hdv : Q.coch.d 1 v = z - z' := hom_f_injective M N Q P hP 2 (by rw [P.hom.comm, hvw, hdw])
  rw [cls_eq_iff]
  exact ⟨v, hdv⟩
end ReciprocityTheory.Coh.InflationTransgression
