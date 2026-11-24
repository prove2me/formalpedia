-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_combD_apply_c0f2a8bfe471
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:59.96751+00:00
-- url     : https://prove2.me/submissions/80b8ef84-098e-4693-9640-dfeab3415d26

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
theorem _root_.solution (J : ∀ k, Finset (ι k)) (n : ℕ) (φ : CombC S J n) (I : CombCell ι J (n + 1)) :
    combD S J n φ I = tD (ext J n φ) I.1.1 := by
  rw [tD, Finset.sum_sigma]
  simp only [combD, LinearMap.pi_apply, LinearMap.sum_apply, rem]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ((∀ l', (Function.update I.1.1 l ((I.1.1 l).erase i) l').Nonempty) ∧
      ∑ l', ((Function.update I.1.1 l ((I.1.1 l).erase i) l').card - 1) = n) ∧
      ∀ l', J l' ⊆ Function.update I.1.1 l ((I.1.1 l).erase i) l'
  · rw [dif_pos h, ext, dif_pos h]; rfl
  · rw [dif_neg h, ext, dif_neg h]; simp
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
