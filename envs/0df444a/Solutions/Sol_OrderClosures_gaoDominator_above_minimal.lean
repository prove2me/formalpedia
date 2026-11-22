-- Prove2me | solution 1 for OrderClosures.gaoDominator_above_minimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:00.509908+00:00
-- url     : https://prove2.me/submissions/9c004e5d-ad20-4bfc-a1df-dca737eed442

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Theorems.Thm_OrderClosures_CNFListLT_trans
public import Theorems.Thm_OrderClosures_CNFStep_trans
public import Theorems.Thm_OrderClosures_cnfExtensionLE_partialOrder_and_subrelation


set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution
    (ξ γ : Ordinal.{u}) {b : C(GaoCompactSpace ξ, ℝ)}
    {ζ : GaoIndex ξ} (hζ : ζ ∈ gaoDominators ξ γ b) :
    ∃ μ ∈ gaoMinimalDominators ξ γ b, cnfExtensionLE μ.1 ζ.1 := by
  classical
  let P : GaoIndex ξ → Prop := fun η ↦
    η ∈ gaoDominators ξ γ b ∧ cnfExtensionLE η.1 ζ.1
  obtain ⟨μ, hμP, hμmin⟩ := exists_minimalFor_of_wellFoundedLT P
    (fun η : GaoIndex ξ ↦ η.1) ⟨ζ, hζ, Or.inl rfl⟩
  refine ⟨μ, ⟨hμP.1, ?_⟩, hμP.2⟩
  intro η hη hημ
  have hηP : P η := ⟨hη,
    cnfExtensionLE_partialOrder_and_subrelation.1.trans
      η.1 μ.1 ζ.1 hημ hμP.2⟩
  have hηleμ := cnfExtensionLE_partialOrder_and_subrelation.2 hημ
  exact Subtype.ext (le_antisymm hηleμ (hμmin hηP hηleμ))
end OrderClosures
