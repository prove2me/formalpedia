-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRegularLocalRing_of_flat_of_closedFibre_c27dad4184d7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:31:43.797906+00:00
-- url     : https://prove2.me/submissions/c08e7806-6b30-4d5a-b03b-9f72122b3ad2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreConditions
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSerreRFlatAscentLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isLocalRing_closedFibre_1cfedabc2710
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ringKrullDim_eq_add_ringKrullDim_closedFibre_2bbf7e020a6c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
  [IsLocalHom (algebraMap R S)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution [IsNoetherianRing S] [Module.Flat R S]
    (hR : IsRegularLocalRing R) (hF : IsRegularLocalRing (S ⧸ (maximalIdeal R).map (algebraMap R S))) :
    IsRegularLocalRing S := by
  have : IsNoetherianRing R := by have := hR; infer_instance
  have := isLocalRing_closedFibre (R := R) (S := S)
  set J := (maximalIdeal R).map (algebraMap R S)
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [ringKrullDim_eq_add_ringKrullDim_closedFibre (R := R), ← (isRegularLocalRing_iff R).mp hR,
    ← (isRegularLocalRing_iff (S ⧸ J)).mp hF]
  suffices h : (maximalIdeal S).spanFinrank ≤
      (maximalIdeal R).spanFinrank + (maximalIdeal (S ⧸ J)).spanFinrank by
    exact_mod_cast h
  have fgR := (maximalIdeal R).fg_of_isNoetherianRing
  have fgF := (maximalIdeal (S ⧸ J)).fg_of_isNoetherianRing
  set s := (maximalIdeal R).generators
  set t := (maximalIdeal (S ⧸ J)).generators
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  let lift : S ⧸ J → S := Function.surjInv hsurj
  set t' := lift '' t
  have ht' : Ideal.Quotient.mk J '' t' = t := by
    rw [Set.image_image]
    simp [lift, Function.surjInv_eq hsurj]
  have : IsLocalHom (Ideal.Quotient.mk J) := IsLocalHom.of_surjective _ hsurj
  have hcomap : (maximalIdeal (S ⧸ J)).comap (Ideal.Quotient.mk J) = maximalIdeal S :=
    maximalIdeal_comap _
  have heq : maximalIdeal S = Ideal.span (algebraMap R S '' s ∪ t') := by
    apply le_antisymm
    · intro x hx
      have hx' : Ideal.Quotient.mk J x ∈ Ideal.map (Ideal.Quotient.mk J) (Ideal.span t') := by
        rw [Ideal.map_span, ht']
        change Ideal.Quotient.mk J x ∈ Submodule.span (S ⧸ J) t
        rw [Submodule.span_generators, ← Ideal.mem_comap, hcomap]
        exact hx
      rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker] at hx'
      rw [Ideal.span_union, sup_comm, ← Ideal.map_span]
      change x ∈ Submodule.span S t' ⊔ Ideal.map (algebraMap R S) (Submodule.span R s)
      rw [Submodule.span_generators]
      exact hx'
    · rw [Ideal.span_le, Set.union_subset_iff]
      constructor
      · rintro _ ⟨y, hy, rfl⟩
        exact map_maximalIdeal_le (algebraMap R S) (Ideal.mem_map_of_mem _ (Submodule.FG.generators_mem _ hy))
      · rintro _ ⟨y, hy, rfl⟩
        rw [SetLike.mem_coe, ← hcomap, Ideal.mem_comap, Function.surjInv_eq hsurj]
        exact Submodule.FG.generators_mem _ hy
  have fins := Submodule.FG.finite_generators fgR
  have fint := Submodule.FG.finite_generators fgF
  rw [heq, ← Submodule.FG.generators_ncard fgR, ← Submodule.FG.generators_ncard fgF]
  refine (Submodule.spanFinrank_span_le_ncard_of_finite ((fins.image _).union (fint.image _))).trans ?_
  exact (Set.ncard_union_le _ _).trans (add_le_add (Set.ncard_image_le fins) (Set.ncard_image_le fint))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
