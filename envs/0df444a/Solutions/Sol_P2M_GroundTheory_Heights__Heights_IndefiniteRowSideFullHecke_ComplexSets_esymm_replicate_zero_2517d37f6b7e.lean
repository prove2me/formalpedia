-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_esymm_replicate_zero_2517d37f6b7e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:31:40.227904+00:00
-- url     : https://prove2.me/submissions/059715d5-68a1-4e46-b864-ecad6560f8f6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCircleArgumentPrinciple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPowerSumsEsymmAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermWeierstrassPreparation

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
open Topology Filter Metric Complex Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {n k : ℕ} (hk : 1 ≤ k) : (Multiset.replicate n (0 : ℂ)).esymm k = 0 := by
  unfold Multiset.esymm
  refine Multiset.sum_eq_zero fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hx
  obtain ⟨hle, hcard⟩ := Multiset.mem_powersetCard.1 ht
  have : t = Multiset.replicate k 0 :=
    Multiset.eq_replicate.2 ⟨hcard, fun b hb => Multiset.eq_of_mem_replicate (Multiset.mem_of_le hle hb)⟩
  rw [this, Multiset.prod_replicate, zero_pow (by omega)]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
