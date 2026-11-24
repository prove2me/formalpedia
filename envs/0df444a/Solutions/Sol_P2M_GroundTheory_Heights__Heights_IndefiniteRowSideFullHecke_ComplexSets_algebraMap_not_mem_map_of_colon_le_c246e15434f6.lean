-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_algebraMap_not_mem_map_of_colon_le_c246e15434f6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:36.497563+00:00
-- url     : https://prove2.me/submissions/3da53694-3fff-4a68-8c72-57fde2e1e611

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
    {y : B} (hy : ∀ r, r * y ∈ I → r ∈ Q) :
    algebraMap B (Localization.AtPrime Q) y ∉ I.map (algebraMap B (Localization.AtPrime Q)) := by
  intro h
  obtain ⟨⟨i, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff Q.primeCompl _).mp h
  rw [← map_mul, IsLocalization.eq_iff_exists Q.primeCompl] at hs
  obtain ⟨c, hc⟩ := hs
  have h1 : (↑c * ↑s) * y ∈ I := by
    rw [show (↑c * ↑s) * y = ↑c * (y * ↑s) by ring, hc]
    exact I.mul_mem_left _ i.2
  have h2 := hy _ h1
  exact (Q.primeCompl.mul_mem c.2 s.2) h2
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
