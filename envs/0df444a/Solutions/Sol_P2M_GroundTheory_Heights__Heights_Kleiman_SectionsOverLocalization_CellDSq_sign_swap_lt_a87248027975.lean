-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sign_swap_lt_a87248027975
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:23.874849+00:00
-- url     : https://prove2.me/submissions/36330ca2-8ff8-421d-9bd5-e80689056605

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DoubleSumEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
noncomputable section
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
theorem _root_.solution {I : ∀ k, Finset (ι k)} {k k' : K} (i : ι k) (i' : ι k') (hi : i ∈ I k)
    (hk : k < k') (h2 : 2 ≤ (I k).card) :
    faceSign I k' i' * faceSign (rem I ⟨k', i'⟩) k i =
      -(faceSign I k i * faceSign (rem I ⟨k, i⟩) k' i') := by
  have hmem : k ∈ Finset.univ.filter (· < k') := Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩
  have hoff : ∑ l ∈ Finset.univ.filter (· < k'), ((Function.update I k ((I k).erase i) l).card - 1) + 1 =
      ∑ l ∈ Finset.univ.filter (· < k'), ((I l).card - 1) := by
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem, Function.update_self,
      Finset.sum_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)],
      Finset.card_erase_of_mem hi]
    omega
  have hlow : ∑ l ∈ Finset.univ.filter (· < k), ((Function.update I k' ((I k').erase i') l).card - 1) =
      ∑ l ∈ Finset.univ.filter (· < k), ((I l).card - 1) :=
    Finset.sum_congr rfl fun l hl => by
      rw [Function.update_of_ne (ne_of_lt ((Finset.mem_filter.1 hl).2.trans hk))]
  unfold faceSign rem
  simp only [Function.update_of_ne hk.ne, Function.update_of_ne hk.ne', hlow]
  rw [← hoff]
  ring
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
