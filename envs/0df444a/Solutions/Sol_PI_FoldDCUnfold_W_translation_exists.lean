-- Prove2me | solution 1 for PI.FoldDCUnfold.W.translation_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:53.372413+00:00
-- url     : https://prove2.me/submissions/4ef5c4fb-a721-4ff9-bedd-c9880cdfb812

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
theorem _root_.solution : TransExists.{u} := by
  intro G _ K H hHK
  classical
  obtain ⟨rep, hrepdef⟩ : ∃ rep : G → G,
      ∀ γ, rep γ = (Quotient.mk (QuotientGroup.rightRel H) γ).out := ⟨_, fun _ => rfl⟩
  have hrep : ∀ γ, γ * (rep γ)⁻¹ ∈ H := fun γ => by
    rw [hrepdef]
    exact QuotientGroup.rightRel_apply.mp
      (Quotient.exact (Quotient.out_eq (Quotient.mk (QuotientGroup.rightRel H) γ)))
  have hrep_eq : ∀ γ γ', γ * γ'⁻¹ ∈ H → rep γ = rep γ' := fun γ γ' h => by
    rw [hrepdef, hrepdef]
    congr 1
    exact Quotient.sound (QuotientGroup.rightRel_apply.mpr (by simpa using H.inv_mem h))
  have hrepK : ∀ γ ∈ K, rep γ ∈ K := fun γ hγ => by
    have h1 : rep γ = (γ * (rep γ)⁻¹)⁻¹ * γ := by group
    rw [h1]
    exact K.mul_mem (K.inv_mem (hHK (hrep γ))) hγ
  refine ⟨rep '' (K : Set G), ?_, ?_⟩
  · rintro _ ⟨γ, hγ, rfl⟩
    exact hrepK γ hγ
  · intro γ hγ
    refine ⟨(⟨γ * (rep γ)⁻¹, hrep γ⟩, ⟨rep γ, γ, hγ, rfl⟩), by simp, ?_⟩
    rintro ⟨⟨s, hs⟩, ⟨e, ⟨γ', hγ', rfl⟩⟩⟩ he
    have he' : s * rep γ' = γ := he
    have h1 : rep γ' = rep γ := by
      have h2 : rep (rep γ') = rep γ' :=
        hrep_eq _ _ (by simpa using H.inv_mem (hrep γ'))
      rw [← h2]
      apply hrep_eq
      rw [← he']
      simpa using H.inv_mem hs
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show s = γ * (rep γ)⁻¹
      calc s = s * rep γ' * (rep γ')⁻¹ := by group
        _ = γ * (rep γ)⁻¹ := by rw [he', h1]
    · exact h1
end PI.FoldDCUnfold.W
