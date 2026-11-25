-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_rem_ins_comm_a1e519b9ef81
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:29:06.571621+00:00
-- url     : https://prove2.me/submissions/ea1c324c-8744-47be-86cf-a14b23ba6bbf

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
theorem _root_.solution (T : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (l : K) (i : ι l) (hi : i ∈ T l)
    (h0 : i₀ ∉ T k) : rem (ins k i₀ T) l i = ins k i₀ (rem T l i) := by
  by_cases h : l = k
  · subst h
    have hne : i₀ ≠ i := fun e => h0 (e ▸ hi)
    rw [rem, ins, ins, rem, Function.update_self, Function.update_self, Function.update_idem,
      Function.update_idem, Finset.erase_insert_of_ne hne]
  · rw [rem, ins, ins, rem, Function.update_of_ne h, Function.update_of_ne (Ne.symm h),
      Function.update_comm (Ne.symm h)]
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
