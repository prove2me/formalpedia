-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.kInv_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:41:59.092156+00:00
-- url     : https://prove2.me/submissions/54654bdf-61f8-40da-a5dd-aadf0e0e3121

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaSt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompInsertNthEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RemoveNthSuccVecCons
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KDKDelApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvarianceContraction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AlternatingMapEqZeroOfSpan
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KugaAbsHolds
import Theorems.Thm_GlobalTheory_CompanionTheory_Invsum_invariance_contraction


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Fin Function
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
namespace PositivityTheory.Rg.Cz
theorem _root_.solution : ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β γ : Type} [Fintype β] (b : β → P) (D : γ → P →ₗ[ℝ] P) (c : β → β → γ → ℝ) (E : γ → Module.End ℂ M), (∀ i j k, c j i k = -c i j k) → (∀ k j, D k (b j) = ∑ i, c i j k • b i) → ∀ {q : ℕ} (ω : P [⋀^Fin q]→ₗ[ℝ] M), (∀ k (Y : Fin q → P), E k (ω Y) = ∑ s, ω (Function.update Y s (D k (Y s)))) → ∀ (k : γ) (J : Fin q → β), ∑ s, ∑ i, (c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i)) = -E k (ω (b ∘ J)) :=
  GlobalTheory.CompanionTheory.Invsum.invariance_contraction
end PositivityTheory.Rg.Cz
