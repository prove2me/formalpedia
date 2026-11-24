-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ringKrullDim_eq_add_ringKrullDim_closedFibre_2bbf7e020a6c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:57.203999+00:00
-- url     : https://prove2.me/submissions/6955ec04-7a09-4a4d-bc32-f93dae2522fd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreConditions
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSerreRFlatAscentLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isLocalRing_closedFibre_1cfedabc2710

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
theorem _root_.solution [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Flat R S] :
    ringKrullDim S = ringKrullDim R + ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  have := isLocalRing_closedFibre (R := R) (S := S)
  have : (maximalIdeal S).LiesOver (maximalIdeal R) := ⟨(maximalIdeal_comap (algebraMap R S)).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R) (maximalIdeal S)
  rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at h
  rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim,
    ← maximalIdeal_height_eq_ringKrullDim, h, WithBot.coe_add]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
