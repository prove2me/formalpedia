-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_homotopy_succ_06f320cbc407
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:20:11.879206+00:00
-- url     : https://prove2.me/submissions/24f83ed8-252c-4942-8210-bf25d6ba3a7d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombContract
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_tH_54fd778341b4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_of_empty_fe169bb191f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_cell_3c1642189a4e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_hh_combD_82ed48b4744a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_tH_succ_1890396c1f6c

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
theorem _root_.solution (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (hJ0 : i₀ ∉ J k) (m : ℕ)
    (φ : CombC S J (m + 1)) (I : CombCell ι J (m + 1)) :
    combD S J m (hh J k i₀ m φ) I + hh J k i₀ (m + 1) (combD S J (m + 1) φ) I +
      tD (corr J k i₀ (m + 1) φ) I.1.1 = φ I := by
  have h := tD_tH k i₀ (ext J (m + 1) φ) (fun T hT => ext_of_empty J (m + 1) φ T hT) I.1.1 I.1.2.1
  rw [tD_tH_succ J k i₀ hJ0 m φ I, ← hh_combD, ext_cell] at h
  rw [← h]; abel
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
