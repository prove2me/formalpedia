-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_cell_ext_28ea0425c440
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:47.279173+00:00
-- url     : https://prove2.me/submissions/8ac0a75f-33a9-4004-898a-79f02139145d

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
theorem _root_.solution {J : ∀ k, Finset (ι k)} {n : ℕ} {I₁ I₂ : CombCell ι J n} (h : I₁.1.1 = I₂.1.1) : I₁ = I₂ :=
  Subtype.ext (Subtype.ext h)
end GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
