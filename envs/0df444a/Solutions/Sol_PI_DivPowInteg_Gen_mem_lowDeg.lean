-- Prove2me | solution 1 for PI.DivPowInteg.Gen.mem_lowDeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:31.684539+00:00
-- url     : https://prove2.me/submissions/40e4b767-470b-4bbb-b753-11d46586c751

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenVan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.DivPowInteg PI.DivPowInteg.Gen
variable {K σ ι : Type} [CommRing K] [Fintype ι]
namespace PI.DivPowInteg.Gen
theorem _root_.solution {f : ι → σ} {t : ℕ} {R : MvPolynomial σ K} :
    R ∈ lowDeg f t ↔ ∀ m ∈ R.support, ∑ i, m (f i) < t := by
  unfold lowDeg
  rw [mem_restrictSupport_iff]
  exact ⟨fun h m hm => h (Finset.mem_coe.mpr hm), fun h m hm => h m (Finset.mem_coe.mp hm)⟩
end PI.DivPowInteg.Gen
