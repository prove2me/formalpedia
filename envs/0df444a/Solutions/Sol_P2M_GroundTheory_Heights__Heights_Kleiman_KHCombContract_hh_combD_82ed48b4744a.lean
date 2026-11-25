-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_hh_combD_82ed48b4744a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:07:12.583808+00:00
-- url     : https://prove2.me/submissions/e30803dc-8823-4b2a-865b-6ac76bb95268

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombContract
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_combD_apply_c0f2a8bfe471
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_cond_ins_9efaac490a1c

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
theorem _root_.solution (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (m : ℕ) (φ : CombC S J m) (I : CombCell ι J m) :
    hh J k i₀ m (combD S J m φ) I = tH k i₀ (tD (ext J m φ)) I.1.1 := by
  rw [hh, tH, tH]
  split_ifs with h0
  · rfl
  · rw [ext, dif_pos (cond_ins J m k i₀ I.1.1 h0 ⟨I.1.2, I.2⟩)]
    congr 1
    exact combD_apply J m φ _
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
