-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLine_isInternal_e70ecd776a09
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:15:48.800938+00:00
-- url     : https://prove2.me/submissions/5bf56b62-bf68-49ad-a89c-7f7c578e2b00

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_LatticeBundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_SingleMemIdealLattice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_mem_coordLine_b2c790866ef5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_single_mem_idealLattice_61eeca6dec4d

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
theorem _root_.solution {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    DirectSum.IsInternal (coordLine a) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro x
    rw [Submodule.disjoint_def]
    intro w hw hw'
    have hle : (⨆ j, ⨆ (_ : j ≠ x), coordLine a j) ≤
        LinearMap.ker ((LinearMap.proj (R := 𝓞 K) (φ := fun _ : Fin n => K) x) ∘ₗ
          (idealLattice a).subtype) :=
      iSup₂_le fun j hj v hv => by
        simp [mem_coordLine.mp hv x (Ne.symm hj)]
    have h0 : (w : Fin n → K) x = 0 := by simpa using hle hw'
    ext y
    by_cases hy : y = x
    · subst hy; simpa using h0
    · simpa using mem_coordLine.mp hw y hy
  · refine eq_top_iff.mpr fun w _ => ?_
    have hw : w = ∑ x, (⟨_, single_mem_idealLattice w x⟩ : idealLattice a) := by
      ext y
      simp [Submodule.coe_sum, Finset.sum_apply, Pi.single_apply]
    rw [hw]
    refine Submodule.sum_mem _ fun x _ => Submodule.mem_iSup_of_mem x (mem_coordLine.mpr ?_)
    intro y hy
    simp [Pi.single_apply, hy]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
