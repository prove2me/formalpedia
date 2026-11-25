-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_range_incl_saturated_7cd10a09373f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:08:27.784554+00:00
-- url     : https://prove2.me/submissions/7518d4b4-24e3-4f49-898f-f20e190eff76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RangeInclSaturated

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
open NumberField NumberField.ComplexEmbedding GroundTheory.Heights₂.Heights
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
theorem _root_.solution {K : Type*} [Field K] [NumberField K]
    {E' E E'' : HermitianBundle K} (Y : HermitianExtension E' E E'') (t : 𝓞 K) (x : E.carrier)
    (ht : t ≠ 0) (hx : t • x ∈ LinearMap.range Y.incl) : x ∈ LinearMap.range Y.incl := by
  rw [← Y.exact.linearMap_ker_eq, LinearMap.mem_ker] at hx ⊢
  rw [map_smul] at hx
  exact (smul_eq_zero.mp hx).resolve_left ht
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
