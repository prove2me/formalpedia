-- Prove2me | solution 1 for PI.FoldMult.UnitaryGroupMassFormula.cnt_encard_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:42.084002+00:00
-- url     : https://prove2.me/submissions/33ab8854-898c-4084-992c-ffe580de5636

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
theorem _root_.solution (Γ : Subgroup G) [DiscreteTopology Γ] (Ω : Set G) (hΩ : IsCompact Ω)
    (x : G) : ∃ N : ℕ∞, N < ⊤ ∧ ∀ y, (cnt Γ Ω x y).encard ≤ N := by
  set K : Set G := (fun p : G × G => x * p.1 * (x * p.2)⁻¹) '' (Ω ×ˢ Ω) with hKdef
  have hK : IsCompact K := (hΩ.prod hΩ).image (by fun_prop)
  have hS : ((Subtype.val : Γ → G) ⁻¹' K).Finite :=
    ((Subgroup.isClosed_of_discrete (H := Γ)).isClosedEmbedding_subtypeVal.isCompact_preimage hK).finite_of_discrete
  refine ⟨((Subtype.val : Γ → G) ⁻¹' K).encard, hS.encard_lt_top, fun y => ?_⟩
  rcases (cnt Γ Ω x y).eq_empty_or_nonempty with h | ⟨γ₀, hγ₀⟩
  · rw [h, Set.encard_empty]
    exact zero_le
  · refine le_trans (Set.encard_le_encard (t := (fun δ : Γ => δ * γ₀) '' ((Subtype.val : Γ → G) ⁻¹' K)) ?_)
      (Set.encard_image_le _ _)
    intro γ hγ
    refine ⟨γ * γ₀⁻¹, ?_, by simp⟩
    refine ⟨(x⁻¹ * ((γ : G) * y), x⁻¹ * ((γ₀ : G) * y)), ⟨hγ, hγ₀⟩, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
end PI.FoldMult.UnitaryGroupMassFormula
