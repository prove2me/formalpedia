-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationIsomorphism.QC_acyc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:00:26.283043+00:00
-- url     : https://prove2.me/submissions/b4d0d340-5cad-48b1-ba26-e4d93e444613

import Definitions.Def_ReciprocityTheory_GroupCohomology_InfIsoA
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfIsoB
import Theorems.Thm_ReciprocityTheory_Coh_InflationIsomorphism_QC_coind
import Theorems.Thm_ReciprocityTheory_Coh_FiniteLevelCohomology_H_succ_trivial
import Theorems.Thm_ReciprocityTheory_Coh_shapiro_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function Topology
noncomputable section
universe u
open ReciprocityTheory.Coh.InflationIsomorphism
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [LocallyCompactSpace G] {N : Subgroup G} [N.Normal]
namespace ReciprocityTheory.Coh.InflationIsomorphism
theorem _root_.solution (M : TRep R G) [DiscreteTopology M.V] {QC : TRep R (G ⧸ N)} {PC : Pair QC (CG M)}
    (hC : IsInvRep (CG M) N QC PC) (m : ℕ) (z : QC.H (m + 1)) : z = 0 := by
  have hq := shapiro_holds R (G ⧸ N) (⊥ : Subgroup (G ⧸ N)) (Mbot M) QC (evC M hC) (QC_coind M hC)
    ⟨fun _ => 1, continuous_const, fun x g => by
      have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.1 x.2)
      rw [hx, one_mul]⟩
  have : Subsingleton (⊥ : Subgroup (G ⧸ N)) :=
    ⟨fun a b => Subtype.ext ((Subgroup.mem_bot.1 a.2).trans (Subgroup.mem_bot.1 b.2).symm)⟩
  refine (hq (m + 1)).1 ?_
  rw [map_zero]
  exact FiniteLevelCohomology.H_succ_trivial _ m _
end ReciprocityTheory.Coh.InflationIsomorphism
