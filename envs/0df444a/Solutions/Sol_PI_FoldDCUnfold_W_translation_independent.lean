-- Prove2me | solution 1 for PI.FoldDCUnfold.W.translation_independent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:53.54813+00:00
-- url     : https://prove2.me/submissions/05b4ade9-3a7d-4318-9172-96d9e5a32c04

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FoldingUnfolding_TransExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FoldingUnfolding_TranslationIndependent

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
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable
open PI PI.FoldDCUnfold PI.FoldDCUnfold.W
universe u
namespace PI.FoldDCUnfold.W
theorem _root_.solution : TransIndep.{u} := by
  intro G _ Γ H T T' hT hT' c hc f hf
  classical
  have hmem : ∀ η : T, (η : G) * c ∈ Γ := fun η => Γ.mul_mem (hT.1 η.2) hc
  choose φ hφ using fun η : T => (hT'.2 _ (hmem η)).exists
  have hfeq : ∀ η : T, f ((η : G) * c) = f ((φ η).2 : G) := fun η => by
    rw [← hφ η, hf _ (φ η).1.2]
  have hinj : Function.Injective (fun η => (φ η).2) := by
    intro η₁ η₂ h12
    have h12' : (φ η₁).2 = (φ η₂).2 := h12
    have e1 : ((φ η₁).1 : G) * ((φ η₂).2 : G) = η₁ * c := by rw [← h12']; exact hφ η₁
    have e2 : ((φ η₂).1 : G) * ((φ η₂).2 : G) = η₂ * c := hφ η₂
    have hk : (((φ η₂).1 : G) * ((φ η₁).1 : G)⁻¹) * η₁ = η₂ := by
      calc (((φ η₂).1 : G) * ((φ η₁).1 : G)⁻¹) * η₁
          = ((φ η₂).1 : G) * ((φ η₁).1 : G)⁻¹ * (η₁ * c) * c⁻¹ := by group
        _ = ((φ η₂).1 : G) * ((φ η₁).1 : G)⁻¹ * (((φ η₁).1 : G) * ((φ η₂).2 : G)) * c⁻¹ := by
          rw [e1]
        _ = (((φ η₂).1 : G) * ((φ η₂).2 : G)) * c⁻¹ := by group
        _ = η₂ * c * c⁻¹ := by rw [e2]
        _ = η₂ := by group
    have hu := (hT.2 (η₂ : G) (hT.1 η₂.2)).unique
      (y₁ := ((1 : H), η₂)) (y₂ := (⟨((φ η₂).1 : G) * ((φ η₁).1 : G)⁻¹,
        H.mul_mem (φ η₂).1.2 (H.inv_mem (φ η₁).1.2)⟩, η₁)) (by simp) hk
    exact (congrArg Prod.snd hu).symm
  have hsurj : Function.Surjective (fun η => (φ η).2) := by
    intro η'
    have hm : (η' : G) * c⁻¹ ∈ Γ := Γ.mul_mem (hT'.1 η'.2) (Γ.inv_mem hc)
    obtain ⟨⟨s, η⟩, hsη, -⟩ := hT.2 _ hm
    have hsη' : (s : G) * η = η' * c⁻¹ := hsη
    refine ⟨η, ?_⟩
    have hy : ((s : G))⁻¹ * η' = η * c := by
      have : (η : G) = (s : G)⁻¹ * (η' * c⁻¹) := by rw [← hsη']; group
      rw [this]
      group
    have hu := (hT'.2 _ (hmem η)).unique (hφ η)
      (y₂ := (⟨(s : G)⁻¹, H.inv_mem s.2⟩, η')) hy
    exact congrArg Prod.snd hu
  calc ∑' η : T, f ((η : G) * c) = ∑' η : T, f ((φ η).2 : G) := tsum_congr hfeq
    _ = ∑' η' : T', f η' :=
      Equiv.tsum_eq (Equiv.ofBijective (fun η => (φ η).2) ⟨hinj, hsurj⟩) (fun η' : T' => f η')
end PI.FoldDCUnfold.W
