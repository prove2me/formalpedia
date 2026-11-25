-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationIsomorphism.QC_coind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:58:33.378605+00:00
-- url     : https://prove2.me/submissions/ce6b7e5b-0a32-47f3-93f3-1a2b375d1332

import Definitions.Def_ReciprocityTheory_GroupCohomology_InfIsoA
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfIsoB
import Theorems.Thm_ReciprocityTheory_Coh_InflationIsomorphism_evC_rho
import Theorems.Thm_ReciprocityTheory_Coh_InflationIsomorphism_emb_disc


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
    (hC : IsInvRep (CG M) N QC PC) : IsCoind (⊥ : Subgroup (G ⧸ N)) (Mbot M) QC (evC M hC) := by
  have := inv_disc hC
  have : DiscreteTopology (Mbot (N := N) M).V := ‹DiscreteTopology M.V›
  have := cmap_disc (G ⧸ N) (Mbot (N := N) M).V
  let j : QC.V → C(G ⧸ N, (Mbot (N := N) M).V) := fun q =>
    ⟨fun y => (evC M hC).u (QC.rho y q),
      (evC M hC).u_cont.comp (QC.cont.comp (f := fun y => (y, q)) (continuous_id.prodMk continuous_const))⟩
  have hj : ∀ q (g : G), j q (g : G ⧸ N) = (PC.u q).1 g := evC_rho M hC
  refine ⟨rfl, j, emb_disc _ fun q q' h => ?_, fun c g => rfl, fun f _ => ?_⟩
  · apply hC.2.1.injective
    refine Subtype.ext (ContinuousMap.ext fun g => ?_)
    rw [← hj, ← hj, h]
  · let F : (CG M).V := ⟨f.comp ⟨QuotientGroup.mk, continuous_quot_mk⟩, fun x g => by
      have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.1 x.2)
      subst hx
      show f ((((1 : (⊥ : Subgroup G)) : G) * g : G) : G ⧸ N) = M.rho 1 (f (g : G ⧸ N))
      rw [map_one, Subgroup.coe_one, one_mul]
      rfl⟩
    obtain ⟨q, hq⟩ := (hC.2.2 F).2 fun n hn => Subtype.ext (ContinuousMap.ext fun h => by
      show f ((h * n : G) : G ⧸ N) = f (h : G ⧸ N)
      rw [QuotientGroup.mk_mul_of_mem h hn])
    refine ⟨q, ContinuousMap.ext fun y => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hj, hq]
    rfl
end ReciprocityTheory.Coh.InflationIsomorphism
