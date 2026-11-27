-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FlatLocalRegularSequence_proof_fccfe0646b28
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:58:35.665039+00:00
-- url     : https://prove2.me/submissions/2d3f2de8-d569-4cd7-bcf1-99cdc0d318d2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularSequence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatLocalRegularSequence
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FlatLocalRegularElement_iterate_65cb9cc80ded

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
open IsLocalRing RingTheory.Sequence Pointwise
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace FlatLocalRegularSequence
theorem _root_.solution (h : FlatLocalRegularElement.Statement) :
    FlatLocalRegularSequence.Statement := by
  intro A B _ _ _ _ _ hA hB hl hflat rs ys hrs hreg hys hfib
  set I := (maximalIdeal A).map (algebraMap A B) with hI
  have hfib' : IsWeaklyRegular (B ⧸ (I • ⊤ : Submodule B B)) ys := by
    have e : (B ⧸ I) ≃ₗ[B] (B ⧸ (I • ⊤ : Submodule B B)) :=
      Submodule.quotEquivOfEq _ _ (by rw [Ideal.smul_eq_mul, Ideal.mul_top])
    rw [← Ideal.Quotient.algebraMap_eq, isWeaklyRegular_map_algebraMap_iff] at hfib
    exact (e.isWeaklyRegular_congr ys).mp hfib
  obtain ⟨hysB, hflatQ⟩ :=
    FlatLocalRegularElement.iterate h hA hB hl ys hys B inferInstance hflat hfib'
  have hrsN : IsWeaklyRegular (B ⧸ (Ideal.ofList ys • (⊤ : Submodule B B))) rs :=
    ((TensorProduct.lid A _).isWeaklyRegular_congr rs).mp (hreg.isWeaklyRegular_rTensor)
  have happ : IsWeaklyRegular B (ys ++ rs.map (algebraMap A B)) :=
    (isWeaklyRegular_append_iff B ys _).mpr
      ⟨hysB, (isWeaklyRegular_map_algebraMap_iff B _ rs).mpr hrsN⟩
  have : IsNoetherian B B := hB
  refine IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal happ List.perm_append_comm ?_
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hys r hr
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => (IsLocalRing.mem_maximalIdeal a).mp (hrs a ha) (isUnit_of_map_unit _ _ hu)
end FlatLocalRegularSequence
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
