-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures.restr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:32:37.781077+00:00
-- url     : https://prove2.me/submissions/592193b4-c22e-4f4c-9e21-93855d717d81

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSumStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBoundHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.style.haveILetI false
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
variable {E : Type*} [CStarAlgebra E]
namespace PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
theorem _root_.solution (S : StarSubalgebra ℂ E) (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (ψ : S.topologicalClosure →ₐ[ℂ] ℂ) :
    ∃ χ : S →⋆ₐ[ℂ] ℂ, (∀ y, ‖χ y‖ ≤ ‖(y : E)‖) ∧
      ∀ y, χ y = ψ (StarSubalgebra.inclusion S.le_topologicalClosure y) := by
  have : IsClosed (S.topologicalClosure : Set E) := S.isClosed_topologicalClosure
  have : Nontrivial S.topologicalClosure :=
    ⟨⟨0, 1, fun h => by simpa using congrArg ψ h⟩⟩
  have : StarHomClass (S.topologicalClosure →ₐ[ℂ] ℂ) S.topologicalClosure ℂ :=
    AlgHomClass.instStarHomClass
  refine ⟨{ ψ.comp (StarSubalgebra.inclusion S.le_topologicalClosure).toAlgHom with
    map_star' := fun y => ?_ }, fun y => ?_, fun y => rfl⟩
  · change ψ (StarSubalgebra.inclusion S.le_topologicalClosure (star y)) =
      star (ψ (StarSubalgebra.inclusion S.le_topologicalClosure y))
    rw [map_star, map_star]
  · change ‖ψ (StarSubalgebra.inclusion S.le_topologicalClosure y)‖ ≤ ‖(y : E)‖
    exact (AlgHom.norm_apply_le_self ψ _).trans_eq rfl
end PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
