-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mul_algebraMap_mem_map_of_le_colon_7284726482a3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:59.73794+00:00
-- url     : https://prove2.me/submissions/69fb53fd-6300-4ab6-8b9b-06b29fb0ff57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatNormalFibres
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ExistsMulEqZeroOfMemAssociatedPrime

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
theorem _root_.solution {B : Type*} [CommRing B] (Q : Ideal B) [Q.IsPrime] (I : Ideal B)
    {y : B} (hy : ∀ r ∈ Q, r * y ∈ I) :
    ∀ m ∈ maximalIdeal (Localization.AtPrime Q),
      m * algebraMap B (Localization.AtPrime Q) y ∈ I.map (algebraMap B (Localization.AtPrime Q)) := by
  intro m hm
  rw [← Localization.AtPrime.map_eq_maximalIdeal] at hm
  have hle : Q.map (algebraMap B (Localization.AtPrime Q)) ≤
      (I.map (algebraMap B (Localization.AtPrime Q))).colon {algebraMap B (Localization.AtPrime Q) y} := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul]
    exact Ideal.mem_map_of_mem _ (hy r hr)
  have := hle hm
  rwa [Submodule.mem_colon_singleton, smul_eq_mul] at this
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
