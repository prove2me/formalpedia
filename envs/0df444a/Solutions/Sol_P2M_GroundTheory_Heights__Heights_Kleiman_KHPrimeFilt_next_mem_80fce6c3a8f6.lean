-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_next_mem_80fce6c3a8f6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:43.930583+00:00
-- url     : https://prove2.me/submissions/ce392225-9bb5-42f1-9804-fa87e9e3056c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHPrimeFilt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} [DirectSum.Decomposition 𝓜]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance 2000] lexDecEq
variable (ι 𝓜)
namespace GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
theorem _root_.solution [IsNoetherianRing S] (A : Submodule (MRingOver S ι) M) :
    (next ι 𝓜 A).1 ∈ 𝓜 (next ι 𝓜 A).2 := by
  unfold next
  split_ifs with h
  · exact (Classical.choose_spec (exists_prime_colon h.1 h.2.1 h.2.2)).1
  · exact Submodule.zero_mem _
end GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
