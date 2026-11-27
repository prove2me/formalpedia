-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalBoundedQuotient_proof_08a57083f268
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:58:45.661607+00:00
-- url     : https://prove2.me/submissions/f169f29c-602d-48ee-ac56-6ee4a012c3cb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalBoundedQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeaklyHolomorphicIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalBoundedQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_eval_div_mul_pow_4b1d77712065

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace NormalBoundedQuotient
theorem _root_.solution (hwi : WeaklyHolomorphicIntegral.Statement)
    (hic : NormalGermIntegrallyClosed.Statement) : NormalBoundedQuotient.Statement := by
  intro σ _ I w N F G hI hIc hw hN hwN hF hG hnv hb

  have hhol : HolomorphicOnSubset (fun z => F z / G z) ((zeroSetIn I ∩ N) \ {z | G z = 0}) := by
    intro z hz
    refine ⟨N ∩ G ⁻¹' {0}ᶜ, hG.continuousOn.isOpen_inter_preimage hN isOpen_compl_singleton,
      ⟨hz.1.2, hz.2⟩, fun z => F z / G z, ?_, fun _ _ => rfl⟩
    have hsub : N ∩ G ⁻¹' {0}ᶜ ⊆ N := Set.inter_subset_left
    simp only [div_eq_mul_inv]
    exact (hF.mono hsub).mul ((hG.mono hsub).inv fun y (hy : y ∈ N ∩ G ⁻¹' {0}ᶜ) => hy.2)
  obtain ⟨V, hVo, hwV, hVN, d, a, ha, heq⟩ :=
    hwi σ I w N G (fun z => F z / G z) hI hIc hw hN hwN hG hnv hhol hb
  refine hic σ I w V F G d a hI hIc hw hVo hwV (hF.mono hVN) (hG.mono hVN) ha hnv ?_
  intro z hz
  rw [monic_eval_div_mul_pow (fun j => a j z) (show G z ≠ 0 from hz.2), heq z hz, mul_zero]
end NormalBoundedQuotient
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
