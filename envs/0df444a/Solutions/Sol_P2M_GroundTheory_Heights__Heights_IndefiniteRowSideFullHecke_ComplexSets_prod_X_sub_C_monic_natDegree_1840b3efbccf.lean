-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_prod_X_sub_C_monic_natDegree_1840b3efbccf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:33:11.849266+00:00
-- url     : https://prove2.me/submissions/3c586394-f8c2-4dea-8716-6e26f96ae5b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeaklyHolomorphicIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalBranchedCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalZerosNowhereDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalTrace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeaklyHolomorphicIntegral

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
open Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {m : ℕ} (a : Fin m → ℂ) :
    (∏ j, (Polynomial.X - Polynomial.C (a j))).Monic ∧
      (∏ j, (Polynomial.X - Polynomial.C (a j))).natDegree = m := by
  refine ⟨Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C (a j), ?_⟩
  rw [Polynomial.natDegree_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C (a j)]
  simp
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
