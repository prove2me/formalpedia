-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_lineCoef_eq_aad90511fb53
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:16.095421+00:00
-- url     : https://prove2.me/submissions/86aacf84-5f02-4315-a525-719a9ec859a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulEqSmulOfFinrankOne

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
open scoped nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {E : HermitianBundle K}
variable {N : Submodule (𝓞 K) E.carrier} (hN : Module.finrank (𝓞 K) N = 1) {l : E.carrier}
  (hl : l ∈ N) (hl0 : l ≠ 0)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
theorem _root_.solution (w : N) {t s : 𝓞 K} (ht : t ≠ 0) (h : t • (w : E.carrier) = s • l) :
    lineCoef hN hl hl0 w = (s : K) / t :=
  lineCoefFun_eq hN hl hl0 w ht h
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
