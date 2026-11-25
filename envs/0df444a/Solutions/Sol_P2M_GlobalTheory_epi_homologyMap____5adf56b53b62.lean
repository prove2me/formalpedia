-- Prove2me | solution 1 for P2M_GlobalTheory_epi_homologyMap____5adf56b53b62
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:34:30.172537+00:00
-- url     : https://prove2.me/submissions/4a570405-12fc-4f07-8d6f-30890ca5dcee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
open GlobalTheory
open ComposableArrows Abelian HomologySequence
variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
include hS₁ hS₂
namespace GlobalTheory
theorem _root_.solution (i : ι) (h₁ : Epi (homologyMap φ.τ₁ i))
    (h₂ : Epi (homologyMap φ.τ₃ i)) (h₃ : ∀ j, c.Rel i j → Mono (homologyMap φ.τ₁ j)) :
    Epi (homologyMap φ.τ₂ i) := by
  by_cases hi : ∃ j, c.Rel i j
  · obtain ⟨j, hij⟩ := hi
    apply epi_of_epi_of_epi_of_mono
      ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δlast.δlast
    · exact (composableArrows₅_exact hS₂ i j hij).δlast.δlast
    · exact h₁
    · exact h₂
    · exact h₃ _ hij
  · refine epi_of_epi_of_epi_of_epi (mapComposableArrows₂ φ i)
      (composableArrows₂_exact hS₂ i) ?_ h₁ h₂
    have := hS₁.epi_g
    apply epi_homologyMap_of_epi_of_not_rel
    simpa using hi
end GlobalTheory
