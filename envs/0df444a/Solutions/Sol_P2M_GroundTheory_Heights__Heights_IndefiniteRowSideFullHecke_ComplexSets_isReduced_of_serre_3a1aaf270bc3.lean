-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isReduced_of_serre_3a1aaf270bc3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:04.795373+00:00
-- url     : https://prove2.me/submissions/2d7c9599-8afc-4f22-9044-f6e984e367aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatNormalFibres
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ExistsMulEqZeroOfMemAssociatedPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_mul_eq_zero_of_mem_associatedPrime_661bba168f30

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
theorem _root_.solution {B : Type*} [CommRing B] [IsNoetherianRing B] (hR : SerreR B 1) (hS : SerreS B 2) :
    IsReduced B := by
  refine ⟨fun x hx => ?_⟩
  by_contra hx0
  obtain ⟨Q, hQ, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing B x hx0
  have hprime : Q.IsPrime := hQ.isPrime
  obtain ⟨n, hn⟩ := hx
  have hxQ : x ∈ Q := hprime.mem_of_pow_mem n (by rw [hn]; exact Q.zero_mem)
  obtain ⟨t, ht, htx⟩ := exists_mul_eq_zero_of_mem_associatedPrime hR hS hQ hxQ
  exact ht (hle (by rw [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]; exact htx))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
