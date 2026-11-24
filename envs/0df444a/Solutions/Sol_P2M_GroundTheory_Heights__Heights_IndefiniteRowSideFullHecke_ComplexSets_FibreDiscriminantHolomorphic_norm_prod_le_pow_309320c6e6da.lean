-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_norm_prod_le_pow_309320c6e6da
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:59.26336+00:00
-- url     : https://prove2.me/submissions/611b88e9-add0-4443-b514-8d483b81224b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFibreDiscriminantHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreDiscriminantHolomorphic

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
open Topology Filter Metric Set
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
variable {σ : Type} [Fintype σ]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
theorem _root_.solution {ι : Type*} (s : Finset ι) (F : ι → ℂ) {C : ℝ} (hC : 1 ≤ C) {n : ℕ}
    (hs : s.card ≤ n) (hF : ∀ i ∈ s, ‖F i‖ ≤ C) : ‖∏ i ∈ s, F i‖ ≤ C ^ n := by
  rw [norm_prod]
  calc ∏ i ∈ s, ‖F i‖ ≤ ∏ _i ∈ s, C := Finset.prod_le_prod (fun i _ => norm_nonneg _) hF
    _ = C ^ s.card := Finset.prod_const C
    _ ≤ C ^ n := pow_le_pow_right₀ hC hs
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
