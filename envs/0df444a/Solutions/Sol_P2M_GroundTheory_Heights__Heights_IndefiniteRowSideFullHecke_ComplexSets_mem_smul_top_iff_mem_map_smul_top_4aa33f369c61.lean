-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_smul_top_iff_mem_map_smul_top_4aa33f369c61
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:00.98157+00:00
-- url     : https://prove2.me/submissions/158db7f9-aa88-4bbd-a848-f13b5782facc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatLocalRegularElement

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
open IsLocalRing TensorProduct
open scoped Pointwise
variable {A B M : Type} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (I : Ideal A) (x : M) :
    x ∈ I • (⊤ : Submodule A M) ↔ x ∈ I.map (algebraMap A B) • (⊤ : Submodule B M) := by
  rw [← Submodule.restrictScalars_mem A (I.map (algebraMap A B) • (⊤ : Submodule B M)) x,
    Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
