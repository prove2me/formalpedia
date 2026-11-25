-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_single_mem_idealLattice_61eeca6dec4d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:03:29.570963+00:00
-- url     : https://prove2.me/submissions/58a9b671-4d10-4db8-8629-b9b019c3589a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_LatticeBundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_SingleMemIdealLattice

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
open scoped nonZeroDivisors
noncomputable section
variable {K : Type} [Field K] [NumberField K]
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
theorem _root_.solution {n : ℕ} {a : Fin n → FractionalIdeal (𝓞 K)⁰ K} (v : idealLattice a)
    (x : Fin n) : (Pi.single x ((v : Fin n → K) x) : Fin n → K) ∈ idealLattice a := by
  have hv := v.2
  unfold idealLattice at hv ⊢
  rw [Submodule.mem_pi] at hv ⊢
  intro y _
  by_cases hy : y = x
  · subst hy; simpa using hv y (Set.mem_univ _)
  · simp [Pi.single_apply, hy]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
