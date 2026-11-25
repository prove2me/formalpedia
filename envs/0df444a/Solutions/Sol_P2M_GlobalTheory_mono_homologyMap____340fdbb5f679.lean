-- Prove2me | solution 1 for P2M_GlobalTheory_mono_homologyMap____340fdbb5f679
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:34:27.173028+00:00
-- url     : https://prove2.me/submissions/07eebffc-8603-47f6-a280-8c89903e029d

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
theorem _root_.solution (j : ι) (h₁ : Mono (homologyMap φ.τ₁ j))
    (h₂ : Mono (homologyMap φ.τ₃ j)) (h₃ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₃ i)) :
    Mono (homologyMap φ.τ₂ j) := by
  by_cases hj : ∃ i, c.Rel i j
  · obtain ⟨i, hij⟩ := hj
    apply mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δ₀.δ₀
    · exact (composableArrows₅_exact hS₂ i j hij).δ₀.δ₀
    · exact h₃ _ hij
    · exact h₁
    · exact h₂
  · refine mono_of_mono_of_mono_of_mono (mapComposableArrows₂ φ j)
      (composableArrows₂_exact hS₁ j) ?_ h₁ h₂
    have := hS₂.mono_f
    apply mono_homologyMap_of_mono_of_not_rel
    simpa using hj
end GlobalTheory
