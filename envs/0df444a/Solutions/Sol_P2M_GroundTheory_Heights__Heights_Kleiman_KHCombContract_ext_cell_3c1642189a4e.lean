-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_cell_3c1642189a4e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:41.649878+00:00
-- url     : https://prove2.me/submissions/533417b9-e966-4a4f-9b94-97e8a4e2e85f

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
theorem _root_.solution (J : ∀ k, Finset (ι k)) (n : ℕ) (φ : CombC S J n) (I : CombCell ι J n) :
    ext J n φ I.1.1 = φ I := by
  rw [ext, dif_pos ⟨I.1.2, I.2⟩]
  rfl
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
