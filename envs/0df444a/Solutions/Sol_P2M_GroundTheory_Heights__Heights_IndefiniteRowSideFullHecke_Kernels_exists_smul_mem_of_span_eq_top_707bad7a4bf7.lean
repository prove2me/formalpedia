-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_exists_smul_mem_of_span_eq_top_707bad7a4bf7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:20:22.397424+00:00
-- url     : https://prove2.me/submissions/2e3d9c54-47a2-42f3-bc84-0dba5864a1a1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_SpanEqTopSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemOfSpanEqTop
import Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_smul_mem_of_span_eq_top_alt_1fef0ba5d336


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (Λ : Submodule (𝓞 K) (Fin n → K)) (hΛ : Submodule.span K (Λ : Set (Fin n → K)) = ⊤)
    (v : Fin n → K) : ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Λ :=
  _root_.GroundTheory.Variant₂.N1.exists_smul_mem_of_span_eq_top_alt Λ hΛ v
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
