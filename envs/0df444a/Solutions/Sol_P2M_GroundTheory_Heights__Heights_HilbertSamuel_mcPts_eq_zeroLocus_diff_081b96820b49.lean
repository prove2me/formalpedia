-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_mcPts_eq_zeroLocus_diff_081b96820b49
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:35.444192+00:00
-- url     : https://prove2.me/submissions/83b458ca-8d36-4500-8278-0149cfe99651

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsClopenComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsIrreducibleConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PClopenComponents
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_not_mem_zeroLocus_multiIrrelevantIdeal_4f8d0c60fed7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (P : Ideal (MRing ι)) :
    mcPts P = zeroLocus ℂ (P.map (MvPolynomial.map (Int.castRingHom ℂ))) \
      zeroLocus ℂ (multiIrrelevantIdeal ι) := by
  ext z
  rw [Set.mem_sdiff, not_mem_zeroLocus_multiIrrelevantIdeal]
  simp only [mcPts, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hb, hv⟩
    refine ⟨fun p hp => ?_, hb⟩
    have hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker (eval z) := by
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact hv f hf
    have h0 := RingHom.mem_ker.mp (hle hp)
    exact h0
  · rintro ⟨hz, hb⟩
    refine ⟨hb, fun f hf => ?_⟩
    have := hz _ (Ideal.mem_map_of_mem _ hf)
    exact this
end GroundTheory.Heights₂.Heights.HilbertSamuel
