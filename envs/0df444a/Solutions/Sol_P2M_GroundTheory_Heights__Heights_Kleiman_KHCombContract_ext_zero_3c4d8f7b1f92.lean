-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_zero_3c4d8f7b1f92
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:18.014037+00:00
-- url     : https://prove2.me/submissions/58ed9945-5768-411b-b65d-36418bfe8146

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
variable {S : Type} [CommRing S]
namespace GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
theorem _root_.solution (J : ∀ k, Finset (ι k)) (n : ℕ) : ext J n (0 : CombC S J n) = 0 := by
  funext T
  rw [ext]
  split_ifs <;> rfl
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
