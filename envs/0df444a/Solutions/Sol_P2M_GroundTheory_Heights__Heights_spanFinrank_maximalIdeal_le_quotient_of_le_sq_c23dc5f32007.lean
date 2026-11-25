-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_spanFinrank_maximalIdeal_le_quotient_of_le_sq_c23dc5f32007
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:41:21.104074+00:00
-- url     : https://prove2.me/submissions/e543e544-dd12-4139-817d-5689a88d0849

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RegularQuotientGenerators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing Ideal
universe u
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {I : Ideal R} (hI : I ≤ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ I)] :
    (maximalIdeal R).spanFinrank ≤ (maximalIdeal (R ⧸ I)).spanFinrank := by
  classical
  obtain ⟨t, htc, hts⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian (maximalIdeal (R ⧸ I)))
  choose g hg using fun y : R ⧸ I => Ideal.Quotient.mk_surjective y
  set s : Finset R := t.image g with hs
  have hmk : ∀ a ∈ maximalIdeal R, Ideal.Quotient.mk I a ∈ maximalIdeal (R ⧸ I) := by
    intro a ha
    have h := Ideal.mem_map_of_mem (Ideal.Quotient.mk I) ha
    rwa [map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective] at h
  have hsm : (s : Set R) ⊆ maximalIdeal R := by
    intro a ha
    simp only [hs, Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha
    obtain ⟨y, hy, rfl⟩ := ha
    have hy' : y ∈ maximalIdeal (R ⧸ I) := hts ▸ Submodule.subset_span hy
    by_contra hn
    have hu : IsUnit (g y) := not_not.mp fun h => hn ((mem_maximalIdeal _).mpr h)
    exact (mem_maximalIdeal _).mp hy' (hg y ▸ hu.map (Ideal.Quotient.mk I))
  have hmap : (Ideal.span (s : Set R)).map (Ideal.Quotient.mk I) = maximalIdeal (R ⧸ I) := by
    rw [Ideal.map_span, hs, Finset.coe_image, ← Set.image_comp,
      show (Ideal.Quotient.mk I) ∘ g = id from funext hg, Set.image_id]
    exact hts
  have hle : maximalIdeal R ≤ Ideal.span (s : Set R) ⊔ maximalIdeal R • maximalIdeal R := by
    intro a ha
    have h1 : Ideal.Quotient.mk I a ∈ (Ideal.span (s : Set R)).map (Ideal.Quotient.mk I) :=
      hmap ▸ hmk a ha
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker] at h1
    exact sup_le_sup_left (hI.trans (le_of_eq (by rw [pow_two, Ideal.smul_eq_mul]))) _ h1
  have hm : maximalIdeal R = Ideal.span (s : Set R) :=
    le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle) (Ideal.span_le.mpr hsm)
  rw [hm, ← htc]
  refine (Submodule.spanFinrank_span_le_ncard_of_finite s.finite_toSet).trans ?_
  rw [Set.ncard_coe_finset]
  exact Finset.card_image_le
end GroundTheory.Heights₂.Heights
