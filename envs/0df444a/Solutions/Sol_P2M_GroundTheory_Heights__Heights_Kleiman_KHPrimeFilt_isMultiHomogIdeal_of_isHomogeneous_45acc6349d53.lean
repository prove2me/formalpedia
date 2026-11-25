-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_isMultiHomogIdeal_of_isHomogeneous_45acc6349d53
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:29:29.857576+00:00
-- url     : https://prove2.me/submissions/01d2755b-1b20-4a00-9999-ddb4da64ca0f

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
namespace GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
theorem _root_.solution {I : Ideal (MRingOver S ι)}
    (h : I.IsHomogeneous (weightedHomogeneousSubmodule S (blockWeight ι))) : IsMultiHomogIdeal I := by
  obtain ⟨T, hT⟩ := (Ideal.IsHomogeneous.iff_exists _ _).mp h
  refine ⟨(↑) '' T, ?_, hT⟩
  rintro f ⟨x, _, rfl⟩
  obtain ⟨b, hb⟩ := x.2
  exact ⟨ofLex b, isMultiHomog_of_isWeightedHomogeneous ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hb)⟩
end GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
