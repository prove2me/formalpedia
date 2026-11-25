-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_ne_zero_facts_17d796702cc2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:26:02.973802+00:00
-- url     : https://prove2.me/submissions/5c164cb1-20aa-44eb-b131-1b539101eb9c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LocCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivCycleNeZeroFacts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MinimalPrimeMultiHomog_proof_00f169244e2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultAtPrimeAtMinimal_proof_af70a5a37a53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialQuotDim_proof_5536281ab8d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SupSpanMultiHomog_proof_861d53cbe2c3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {O : Type u} [CommRing O] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} {P : Ideal (MRing ι O)} (hP : IsMultiHomogIdeal P) {f : MRing ι O} {e : K → ℕ}
    (hf : IsMultiHomog f e) {W : Ideal (MRing ι O)} (h : divCycle P f W ≠ 0) :
    W.IsPrime ∧ IsRelevant W ∧ P ≤ W ∧ IsMultiHomogIdeal W := by
  unfold divCycle at h
  split_ifs at h with hW
  · obtain ⟨hmin, hrel⟩ := hW
    refine ⟨hmin.1.1, hrel, le_trans le_sup_left hmin.1.2, ?_⟩
    exact MinimalPrimeMultiHomog.proof O K ι _ W (SupSpanMultiHomog.proof O K ι P f e hP hf) hmin
  · exact absurd rfl h
end GroundTheory.Heights₂.Heights.NumbersDVR
