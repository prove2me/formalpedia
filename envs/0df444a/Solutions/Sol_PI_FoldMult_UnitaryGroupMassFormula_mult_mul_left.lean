-- Prove2me | solution 1 for PI.FoldMult.UnitaryGroupMassFormula.mult_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:38.182523+00:00
-- url     : https://prove2.me/submissions/4ae64274-50d9-4a11-af82-2e58ad4a7cc0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FoldMult
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MultiplicityMeasurability_MeasurableMult

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
open PI PI.FoldMult PI.FoldMult.UnitaryGroupMassFormula
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
namespace PI.FoldMult.UnitaryGroupMassFormula
theorem _root_.solution (Γ : Subgroup G) (Ω : Set G) (γ : G) (hγ : γ ∈ Γ) (x : G) :
    Formalism.L2.SG.FoldBound.mult Γ Ω (γ * x) = Formalism.L2.SG.FoldBound.mult Γ Ω x := by
  unfold Formalism.L2.SG.FoldBound.mult
  refine iSup_congr fun y => ?_
  have hs : ({δ : Γ | (γ * x)⁻¹ * ((δ : G) * y) ∈ Ω} : Set Γ) =
      (fun ε : Γ => (⟨γ, hγ⟩ : Γ) * ε) '' {ε : Γ | x⁻¹ * ((ε : G) * y) ∈ Ω} := by
    ext δ
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hδ
      refine ⟨(⟨γ, hγ⟩ : Γ)⁻¹ * δ, ?_, by simp⟩
      simpa [mul_assoc] using hδ
    · rintro ⟨ε, hε, rfl⟩
      simpa [mul_assoc] using hε
  rw [hs, Set.InjOn.encard_image (mul_right_injective _).injOn]
end PI.FoldMult.UnitaryGroupMassFormula
