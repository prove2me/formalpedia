-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_eq_sum_range_6018055aec67
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:47.345123+00:00
-- url     : https://prove2.me/submissions/11c68949-0f0c-4886-8e5a-c8c0a2682995

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PevEqZeroOfPresentation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_evalAt_apply_3dcf9480b1b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_C_84d2b4612e3e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_X_1c14eb6f22af
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.evalAt_apply
attribute [local simp] GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.pev_C
attribute [local simp] GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.pev_X

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
variable {d : ℕ} {y₀ : Fin d → ℂ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (H : (analyticSubring y₀)[X]) {n : ℕ} (hn : H.natDegree < n) (y : Fin d → ℂ)
    (t : ℂ) : pev y t H = ∑ i ∈ Finset.range n, (H.coeff i : (Fin d → ℂ) → ℂ) y * t ^ i := by
  simp only [pev, RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, coe_mapRingHom, eval_map]
  rw [eval₂_eq_sum_range' _ hn]
  rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
