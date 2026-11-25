-- Prove2me | solution 1 for PI.FoldMult.UnitaryGroupMassFormula.isClosed_hitSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:40:31.616606+00:00
-- url     : https://prove2.me/submissions/45e6db7c-7d75-4113-9f6f-967d6ae64dd1

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
theorem _root_.solution (Γ : Subgroup G) (Ω : Set G) (hΩ : IsCompact Ω) (A : Finset Γ) :
    IsClosed (hitSet Γ Ω A) := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · convert isClosed_univ
    ext x
    simp [hitSet]
  · have hΩc : IsClosed Ω := hΩ.isClosed
    have : CompactSpace Ω := isCompact_iff_compactSpace.1 hΩ
    have hC : IsClosed {p : G × Ω | ∀ a ∈ A, p.1⁻¹ * ((a : G) * ((a₀ : G)⁻¹ * (p.1 * (p.2 : G)))) ∈ Ω} := by
      have hI : {p : G × Ω | ∀ a ∈ A, p.1⁻¹ * ((a : G) * ((a₀ : G)⁻¹ * (p.1 * (p.2 : G)))) ∈ Ω} =
          ⋂ a ∈ A, (fun p : G × Ω => p.1⁻¹ * ((a : G) * ((a₀ : G)⁻¹ * (p.1 * (p.2 : G))))) ⁻¹' Ω := by
        ext p
        simp
      rw [hI]
      exact isClosed_biInter fun a _ => hΩc.preimage (by fun_prop)
    have hEq : hitSet Γ Ω A =
        Prod.fst '' {p : G × Ω | ∀ a ∈ A, p.1⁻¹ * ((a : G) * ((a₀ : G)⁻¹ * (p.1 * (p.2 : G)))) ∈ Ω} := by
      ext x
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨(x, ⟨x⁻¹ * ((a₀ : G) * y), hy a₀ ha₀⟩), fun a ha => ?_, rfl⟩
        simpa [mul_assoc] using hy a ha
      · rintro ⟨p, hp, rfl⟩
        exact ⟨(a₀ : G)⁻¹ * (p.1 * (p.2 : G)), hp⟩
    rw [hEq]
    exact isClosedMap_fst_of_compactSpace _ hC
end PI.FoldMult.UnitaryGroupMassFormula
