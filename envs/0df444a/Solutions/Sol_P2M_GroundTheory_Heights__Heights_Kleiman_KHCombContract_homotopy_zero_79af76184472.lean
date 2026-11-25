-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_homotopy_zero_79af76184472
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:45.626496+00:00
-- url     : https://prove2.me/submissions/8a0e8da9-ca24-46fa-9a9b-6758b035126a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombContract
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_tH_54fd778341b4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_of_empty_fe169bb191f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_cell_3c1642189a4e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_hh_combD_82ed48b4744a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_tH_zero_14c81d40cb21

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
theorem _root_.solution (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (φ : CombC S J 0) (I : CombCell ι J 0) :
    hh J k i₀ 0 (combD S J 0 φ) I + tD (corr J k i₀ 0 φ) I.1.1 = φ I := by
  have h := tD_tH k i₀ (ext J 0 φ) (fun T hT => ext_of_empty J 0 φ T hT) I.1.1 I.1.2.1
  rw [tD_tH_zero, ← hh_combD, ext_cell] at h
  rw [← h]; abel
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
