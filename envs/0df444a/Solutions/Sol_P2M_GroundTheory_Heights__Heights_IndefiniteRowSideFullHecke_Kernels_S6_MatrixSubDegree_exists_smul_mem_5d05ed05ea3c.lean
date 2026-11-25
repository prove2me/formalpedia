-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_exists_smul_mem_5d05ed05ea3c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:10:39.280305+00:00
-- url     : https://prove2.me/submissions/56e3a1ea-11c6-4d77-ad47-9467506c59cb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsSmulMemFamilyOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CardQuotientEqGenIndex
import Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_smul_mem_family_of_span_eq_top_39d555038d1f


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
open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights TensorProduct
open scoped nonZeroDivisors ComplexOrder
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
namespace S6.MatrixSubDegree
theorem _root_.solution {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (𝓞 K) (Fin N → K)) (hspan : Submodule.span K (M : Set (Fin N → K)) = ⊤)
    {ι : Type*} [Fintype ι] (v : ι → Fin N → K) :
    ∃ t : 𝓞 K, t ≠ 0 ∧ ∀ i, algebraMap (𝓞 K) K t • v i ∈ M :=
  _root_.GroundTheory.Variant₂.N1.exists_smul_mem_family_of_span_eq_top M hspan v
end S6.MatrixSubDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
