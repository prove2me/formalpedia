-- Prove2me | solution 1 for ReciprocityTheory.Coh.FiniteLevelCohomology.exists_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:06:06.841804+00:00
-- url     : https://prove2.me/submissions/4f5230d2-624c-46af-9f3a-fbee10eaeeac

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Theorems.Thm_ReciprocityTheory_Coh_FiniteLevelCohomology_exists_open_normal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Topology
open scoped Pointwise
universe u
open ReciprocityTheory.Coh.FiniteLevelCohomology
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.FiniteLevelCohomology
theorem _root_.solution [CompactSpace G] [TotallyDisconnectedSpace G] (M : TRep R G)
    [DiscreteTopology M.V] (n : ℕ) (x : M.H n) :
    ∃ (N : Subgroup G) (_ : N.Normal), IsOpen (N : Set G) ∧ ∀ (Q : TRep R (G ⧸ N)) (P : Pair Q M),
      IsInvRep M N Q P → x ∈ LinearMap.range (P.hom.H n) := by
  obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hc' : M.coch.d n c = 0 := hc
  obtain ⟨N, hN, hNo, hconst, hfix⟩ := exists_open_normal M c.1 c.2
  refine ⟨N, hN, hNo, fun Q P hP => ?_⟩
  have := QuotientGroup.discreteTopology hNo
  obtain ⟨hφ, hemb, hrange⟩ := hP
  have hval : ∀ q : Fin n → G ⧸ N, ∃ y, P.u y = c.1 (fun i => (q i).out) :=
    fun q => (hrange _).2 fun a ha => hfix _ a ha
  choose f' hf' using hval
  have hout : ∀ g : Fin n → G,
      c.1 (fun i => (QuotientGroup.mk (s := N) (g i) : G ⧸ N).out) = c.1 g := by
    intro g
    choose v hv using fun i => QuotientGroup.mk_out_eq_mul N (g i)
    have e : (fun i => (QuotientGroup.mk (s := N) (g i) : G ⧸ N).out) = g * fun i => (v i : G) :=
      funext fun i => hv i
    rw [e]
    exact hconst g _ fun i => (v i).2
  have hPf : ∀ g : Fin n → G, P.u (f' fun i => P.φ (g i)) = c.1 g := by
    intro g
    rw [hφ]
    exact (hf' _).trans (hout g)
  let F : Q.coch.X n := ⟨f', continuous_of_discreteTopology⟩
  have h2 : P.hom.f n F = c := Subtype.ext (funext hPf)
  have hF : Q.coch.d n F = 0 := by
    have h1 : P.hom.f (n + 1) (Q.coch.d n F) = M.coch.d n (P.hom.f n F) := P.hom.comm n F
    rw [h2, hc'] at h1
    apply Subtype.ext
    funext q
    have h3 := congrFun (congrArg Subtype.val h1) (fun i => (q i).out)
    have h4 : (fun i => P.φ ((q i).out)) = q := by
      funext i
      rw [hφ]
      exact QuotientGroup.out_eq' (q i)
    change P.u ((Q.coch.d n F).1 fun i => P.φ ((q i).out)) = 0 at h3
    rw [h4] at h3
    exact hemb.injective (h3.trans (map_zero _).symm)
  refine ⟨Submodule.Quotient.mk ⟨F, hF⟩, ?_⟩
  rw [Cx.Hom.H, Submodule.mapQ_apply]
  congr 1
  exact Subtype.ext h2
end ReciprocityTheory.Coh.FiniteLevelCohomology
