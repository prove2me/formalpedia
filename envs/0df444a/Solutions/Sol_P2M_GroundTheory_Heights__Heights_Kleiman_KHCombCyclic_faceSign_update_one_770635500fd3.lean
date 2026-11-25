-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_faceSign_update_one_770635500fd3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:52.905719+00:00
-- url     : https://prove2.me/submissions/ea6bd0f9-a773-49c4-a5d6-c660e18c7f5e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombCyclicSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombCyclic

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
open GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
namespace GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
theorem _root_.solution (A : ∀ k, Finset (ι k)) {k l : K} (hl : l ≠ k) (i : ι l) (v : Finset (ι k))
    (hA : (A k).card = 1) (hv : v.card = 1) :
    KH.faceSign (Function.update A k v) l i = KH.faceSign A l i := by
  have hs : ∑ m ∈ Finset.univ.filter (· < l), ((Function.update A k v m).card - 1) =
      ∑ m ∈ Finset.univ.filter (· < l), ((A m).card - 1) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : m = k
    · rw [hm, Function.update_self, hv, hA]
    · rw [Function.update_of_ne hm]
  unfold KH.faceSign
  rw [Function.update_of_ne hl, hs]
end GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
