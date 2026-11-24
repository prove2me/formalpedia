-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_faceOK_congr_1857042b9c83
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:47.675524+00:00
-- url     : https://prove2.me/submissions/bc99dc12-d44b-4881-8422-c469a7e763a6

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
theorem _root_.solution {J : ∀ k, Finset (ι k)} {n : ℕ} {k : K} (hJ : J k = ∅) {G G' : ∀ k, Finset (ι k)}
    (hc : (G k).card = (G' k).card) (ho : ∀ m, m ≠ k → G m = G' m) : FaceOK J n G ↔ FaceOK J n G' := by
  have hcard : ∀ m, (G m).card = (G' m).card := fun m => by
    by_cases hm : m = k
    · rw [hm]; exact hc
    · rw [ho m hm]
  have hsub : ∀ m, J m ⊆ G m ↔ J m ⊆ G' m := fun m => by
    by_cases hm : m = k
    · rw [hm, hJ]; simp
    · rw [ho m hm]
  simp only [FaceOK, ← Finset.card_pos, hcard, hsub]
end GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
