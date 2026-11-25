-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_mem_coordLine_b2c790866ef5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:53:45.90682+00:00
-- url     : https://prove2.me/submissions/9b384821-0311-49da-b918-5a8d29142c59

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
theorem _root_.solution {n : ℕ} {a : Fin n → FractionalIdeal (𝓞 K)⁰ K} {x : Fin n}
    {w : idealLattice a} : w ∈ coordLine a x ↔ ∀ y, y ≠ x → (w : Fin n → K) y = 0 := by
  simp only [coordLine, satSub, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.restrictScalars_mem, Set.range_const, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, ht⟩ y hy
    rw [← ht]
    simp [hy]
  · intro h
    refine ⟨(w : Fin n → K) x, funext fun y => ?_⟩
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy, h y hy]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
