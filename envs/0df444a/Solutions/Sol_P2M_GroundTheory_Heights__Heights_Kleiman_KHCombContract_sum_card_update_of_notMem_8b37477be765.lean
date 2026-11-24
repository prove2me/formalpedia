-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sum_card_update_of_notMem_8b37477be765
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:36.052698+00:00
-- url     : https://prove2.me/submissions/4150eebd-658d-486c-a9d1-89ee266b3683

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombContract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
namespace GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
theorem _root_.solution (T : ∀ k, Finset (ι k)) (l : K) (A : Finset (ι l)) (s : Finset K) (hl : l ∉ s) :
    ∑ x ∈ s, ((Function.update T l A x).card - 1) = ∑ x ∈ s, ((T x).card - 1) :=
  Finset.sum_congr rfl fun x hx => by rw [Function.update_of_ne (by rintro rfl; exact hl hx)]
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
