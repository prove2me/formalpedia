-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_comp_perm_e85b949ac36d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:49:14.647315+00:00
-- url     : https://prove2.me/submissions/5982e2c4-0f9f-46a6-837d-b8161face587

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumEventual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumAdditive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumPointDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_InterSumEventuallyEqInterNum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_eq_foldl_map_62765374a469
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_assoc_e501c3cc2859
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_comm_31b97c8bd736


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
open MvPolynomial Filter
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {n : ℕ} (L : Fin n → SubSystem S x Ω) (σ : Equiv.Perm (Fin n))
    (T : Finset (Fin n)) :
    tensorSub (fun i => L (σ i)) T = tensorSub L (T.map σ.toEmbedding) := by
  rw [tensorSub_eq_foldl_map, tensorSub_eq_foldl_map]
  have hp : (((List.finRange n).filter (· ∈ T)).map σ).Perm
      ((List.finRange n).filter (· ∈ T.map σ.toEmbedding)) := by
    rw [List.perm_ext_iff_of_nodup (((List.nodup_finRange n).filter _).map σ.injective)
      ((List.nodup_finRange n).filter _)]
    intro a
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      Finset.mem_map_equiv]
    constructor
    · rintro ⟨b, hb, rfl⟩
      simpa using hb
    · intro ha
      exact ⟨σ.symm a, ha, by simp⟩
  have hfun : (fun i => L (σ i)) = L ∘ σ := rfl
  rw [hfun, ← List.map_map]
  exact (hp.map L).foldl_eq' (fun F _ P _ Q => by
    rw [SubSystem.twist_assoc, SubSystem.twist_comm F, ← SubSystem.twist_assoc]) _
end GroundTheory.Heights₂.Heights.Kleiman
