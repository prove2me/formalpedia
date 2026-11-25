-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTransgression.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:27:59.502392+00:00
-- url     : https://prove2.me/submissions/61dde446-7846-43ab-9431-cbde4f2072f9

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionA
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionB
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_hom_f_injective
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_inflation_hom_degree_two_apply
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_descend2
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_oneCochain_apply_fin_one
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_oneDifferential_val
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_wach_d1_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_exists_ext_cochain
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_inflD_of_ext


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
theorem _root_.solution [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [DiscreteTopology M.V]
    (hNc : IsClosed (N : Set G)) (f0 : (M.resSub N).coch.X 1) (hf : (M.resSub N).coch.d 1 f0 = 0)
    (hinv : ∀ s : G, ∃ m : M.V, ∀ n : N, M.rho s (ev1 M N f0 (cj N s n)) - ev1 M N f0 n = M.rho n m - m) :
    ∃ (y : M.coch.X 1) (z : Q.coch.X 2) (_ : Q.coch.d 2 z = 0), M.coch.d 1 y = P.hom.f 2 z ∧
      (Pair.res M N.subtype continuous_subtype_val).hom.f 1 y = f0 := by
  have hfc := (wach_d1_eq_zero_iff (M.resSub N) f0).1 hf
  obtain ⟨y0, hy0c, hy0N, h2, h3⟩ := exists_ext_cochain M N hNc (ev1 M N f0)
    ((show Continuous f0.1 from f0.2).comp (continuous_pi fun _ => continuous_id)) (fun a b => hfc a b) hinv
  have hDc : Continuous fun p : G × G => D1 M y0 p.1 p.2 :=
    ((M.cont.comp (continuous_fst.prodMk (hy0c.comp continuous_snd))).sub
      (hy0c.comp (continuous_fst.mul continuous_snd))).add (hy0c.comp continuous_fst)
  obtain ⟨z, hz⟩ := descend2 M N Q P hP (D1 M y0) hDc (inflD_of_ext M N _ y0 h2 h3)
  let y : M.coch.X 1 := ⟨fun g => y0 (g 0), hy0c.comp (continuous_apply 0)⟩
  have hd : M.coch.d 1 y = P.hom.f 2 z := Subtype.ext (funext fun g => by
    have hg : g = ![g 0, g 1] := by funext i; fin_cases i <;> rfl
    rw [hg, oneDifferential_val, inflation_hom_degree_two_apply M N Q P hP, hz]; rfl)
  have hzc : Q.coch.d 2 z = 0 := hom_f_injective M N Q P hP 3 (by
    rw [map_zero, P.hom.comm, ← hd]; exact M.coch.dd 1 y)
  refine ⟨y, z, hzc, hd, Subtype.ext (funext fun g => ?_)⟩
  show y0 (g 0 : G) = f0.1 g
  rw [hy0N]
  exact (oneCochain_apply_fin_one _ f0 g).symm
end ReciprocityTheory.Coh.InflationTransgression
