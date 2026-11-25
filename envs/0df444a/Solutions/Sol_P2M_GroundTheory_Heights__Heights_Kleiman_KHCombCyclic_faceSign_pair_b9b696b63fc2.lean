-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_faceSign_pair_b9b696b63fc2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:47.492863+00:00
-- url     : https://prove2.me/submissions/89bebbcb-a5ad-4d4f-8d06-012ccc38e4a8

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
theorem _root_.solution (A : ∀ k, Finset (ι k)) (k : K) {a b : ι k} (hab : a < b) (he : A k = {a, b}) :
    KH.faceSign A k b = - KH.faceSign A k a := by
  have h1 : ((A k).filter (· < a)).card = 0 := by
    rw [Finset.card_eq_zero, he]
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
    rintro (rfl | rfl)
    · exact lt_irrefl _
    · exact not_lt.mpr hab.le
  have h2 : ((A k).filter (· < b)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨a, ?_⟩
    rw [he]
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · rfl
      · exact absurd h (lt_irrefl _)
    · rintro rfl
      exact ⟨Or.inl rfl, hab⟩
  unfold KH.faceSign
  rw [h1, h2, pow_add, pow_add]
  ring
end GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
