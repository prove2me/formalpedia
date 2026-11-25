-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_hh_5b992995b6b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:07:12.386656+00:00
-- url     : https://prove2.me/submissions/5c01efed-6ed2-4fb0-97c7-60cdf9ce5bbf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombContract
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_cond_of_ins_e966a7d8f2f2

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
    (T : ∀ k, Finset (ι k)) (hk : (T k).Nonempty) :
    ext J m (hh J k i₀ m φ) T = tH k i₀ (ext J (m + 1) φ) T := by
  by_cases hc : ((∀ l, (T l).Nonempty) ∧ ∑ l, ((T l).card - 1) = m) ∧ ∀ l, J l ⊆ T l
  · rw [ext, dif_pos hc]; rfl
  · rw [ext, dif_neg hc, tH]
    split_ifs with h0
    · rfl
    · rw [ext, dif_neg (fun h => hc (cond_of_ins J m k i₀ hJ0 T h0 hk h)), smul_zero]
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
