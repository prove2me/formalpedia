-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_sumBasis_apply_2327b92b9453
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:32:34.247584+00:00
-- url     : https://prove2.me/submissions/7d0104f1-e956-4c5f-9b6a-8e828013b211

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_CommonDenominator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_LatticeBundleObjects

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
open GroundTheory.Heights₂.Heights.ComplexAt
open scoped nonZeroDivisors ComplexOrder
noncomputable section
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
theorem _root_.solution {n m k : ℕ} (b : Fin m → Fin n → K) (c : Fin k → Fin n → K)
    (hli : LinearIndependent K (Sum.elim b c)) (hmk : m + k = n) (i : Fin m ⊕ Fin k) :
    sumBasis b c hli hmk i = Sum.elim b c i := by
  simp [sumBasis, Module.Basis.mk_apply]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
