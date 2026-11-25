-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_tH_succ_1890396c1f6c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:45:07.203432+00:00
-- url     : https://prove2.me/submissions/eac292ea-5457-4729-9a26-f84238d748bf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombContract
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_add_46340cde44a8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_of_empty_fe169bb191f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_combD_apply_c0f2a8bfe471
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_hh_5b992995b6b6

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
theorem _root_.solution (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (hJ0 : i₀ ∉ J k) (m : ℕ) (φ : CombC S J (m + 1))
    (I : CombCell ι J (m + 1)) :
    tD (tH k i₀ (ext J (m + 1) φ)) I.1.1 =
      combD S J m (hh J k i₀ m φ) I + tD (corr J k i₀ (m + 1) φ) I.1.1 := by
  have : tH k i₀ (ext J (m + 1) φ) = fun T => ext J m (hh J k i₀ m φ) T + corr J k i₀ (m + 1) φ T := by
    funext T
    rw [corr]
    by_cases hT : T k = ∅
    · rw [if_pos hT, ext_of_empty J m _ T ⟨k, hT⟩, zero_add]
    · rw [if_neg hT, add_zero, ext_hh J k i₀ hJ0 m φ T (Finset.nonempty_iff_ne_empty.mpr hT)]
  rw [this, tD_add, combD_apply]
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
