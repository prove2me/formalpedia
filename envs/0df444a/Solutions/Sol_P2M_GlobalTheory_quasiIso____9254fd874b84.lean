-- Prove2me | solution 1 for P2M_GlobalTheory_quasiIso____9254fd874b84
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:46:09.811536+00:00
-- url     : https://prove2.me/submissions/631bb194-cbe1-477e-9373-86afb7d91d9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_P2M_GlobalTheory_mono_homologyMap____340fdbb5f679
import Theorems.Thm_P2M_GlobalTheory_epi_homologyMap____5adf56b53b62

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
theorem _root_.solution (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have := mono_homologyMap_τ₂ φ hS₁ hS₂ i inferInstance inferInstance fun _ _ => inferInstance
  have := epi_homologyMap_τ₂ φ hS₁ hS₂ i inferInstance inferInstance fun _ _ => inferInstance
  apply isIso_of_mono_of_epi
end GlobalTheory
