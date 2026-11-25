-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_not_faceOK_of_card_one_ac09a1e47140
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:53.559223+00:00
-- url     : https://prove2.me/submissions/3746ba57-2e70-4897-8462-52d437519262

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
theorem _root_.solution {J : ∀ k, Finset (ι k)} {n : ℕ} (A : ∀ k, Finset (ι k)) (l : K) {i : ι l}
    (hi : i ∈ A l) (h : (A l).card = 1) : ¬ FaceOK J n (Function.update A l ((A l).erase i)) := fun h' => by
  have := h'.1.1 l
  rw [Function.update_self, ← Finset.card_pos, Finset.card_erase_of_mem hi, h] at this
  exact lt_irrefl 0 this
end GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
