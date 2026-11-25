-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_LatticeAsBundle_hypotheses_inhabited_2b13e1235568
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:14:26.519962+00:00
-- url     : https://prove2.me/submissions/8a7ad4c3-66de-451b-8780-6a87e8a7843e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsRest

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
open scoped nonZeroDivisors
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
namespace S6.LatticeAsBundle
theorem _root_.solution :
    let a : Fin 2 → FractionalIdeal (𝓞 ℚ)⁰ ℚ := fun _ => 1
    let d : (ℚ →+* ℂ) → Fin 2 → ℝ := fun _ _ => 1
    let b : Fin 1 → Fin 2 → ℚ := fun _ => Pi.single 0 1
    let c : Fin 1 → Fin 2 → ℚ := fun _ => Pi.single 1 1
    (∀ x, a x ≠ 0) ∧ (∀ σ x, 0 < d σ x) ∧ (∀ σ x, d (conjugate σ) x = d σ x) ∧
      LinearIndependent ℚ (Sum.elim b c) ∧ 1 + 1 = 2 := by
  intro a d b c
  refine ⟨fun _ => one_ne_zero, fun _ _ => one_pos, fun _ _ => rfl, ?_, rfl⟩
  have h : Sum.elim b c = (Pi.basisFun ℚ (Fin 2)) ∘ finSumFinEquiv := by
    funext i
    rcases i with i | i <;> fin_cases i
    · simp [b, Pi.basisFun_apply]
      rfl
    · simp [c, Pi.basisFun_apply]
      rfl
  rw [h]
  exact (Pi.basisFun ℚ (Fin 2)).linearIndependent.comp _ finSumFinEquiv.injective
end S6.LatticeAsBundle
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
