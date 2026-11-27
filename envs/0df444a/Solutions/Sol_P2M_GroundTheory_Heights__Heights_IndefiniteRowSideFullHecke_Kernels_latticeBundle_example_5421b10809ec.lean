-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_latticeBundle_example_5421b10809ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:59:13.031261+00:00
-- url     : https://prove2.me/submissions/9e81345c-868d-4210-b93a-abaf53cfc891

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_CommonDenominator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_LatticeBundleObjects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_matrixMetric_inner_one_tmul_c11a04f23944

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
theorem _root_.solution :
    let a : Fin 2 → FractionalIdeal (𝓞 ℚ)⁰ ℚ := fun _ => 1
    let d : (ℚ →+* ℂ) → Fin 2 → ℝ := fun _ _ => 1
    ∃ hd : ∀ σ x, 0 < d σ x, ∃ hc : ∀ σ x, d (conjugate σ) x = d σ x,
    ∃ v : (latticeBundle a d hd hc).carrier,
      ((latticeBundle a d hd hc).metric.form ratEmbedding).inner
        ((1 : ComplexAt ratEmbedding) ⊗ₜ[𝓞 ℚ] v) ((1 : ComplexAt ratEmbedding) ⊗ₜ[𝓞 ℚ] v) = 1 := by
  intro a d
  have hv : (Pi.single 0 1 : Fin 2 → ℚ) ∈ idealLattice a := by
    rw [idealLattice, Submodule.mem_pi]
    intro i _
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff]
    by_cases h : i = 0
    · subst h; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [h]⟩
  refine ⟨fun _ _ => one_pos, fun _ _ => rfl, ⟨_, hv⟩, ?_⟩
  · refine (matrixMetric_inner_one_tmul (idealLattice a) (diagMetric d)
      (diagMetric_posDef fun _ _ => one_pos) (diagMetric_conj fun _ _ => rfl) ratEmbedding
      ⟨_, hv⟩ ⟨_, hv⟩).trans ?_
    simp [embVec, diagMetric, dotProduct, Fin.sum_univ_two, d]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
