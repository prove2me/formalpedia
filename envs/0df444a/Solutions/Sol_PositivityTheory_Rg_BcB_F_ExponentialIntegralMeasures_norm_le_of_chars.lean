-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures.norm_le_of_chars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:39:22.365195+00:00
-- url     : https://prove2.me/submissions/85c8fdbf-07c6-4c83-a0b8-8d5032f84c96

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
    (x : E) (hx : x ∈ S) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ ψ : S.topologicalClosure →ₐ[ℂ] ℂ,
      ‖ψ (StarSubalgebra.inclusion S.le_topologicalClosure ⟨x, hx⟩)‖ ≤ c) : ‖x‖ ≤ c := by
  have : IsClosed (S.topologicalClosure : Set E) := S.isClosed_topologicalClosure
  have hs' : ∀ x y : S, x * y = y * x := fun x y => Subtype.ext (hS _ x.2 _ y.2)
  letI : NormedCommRing S.topologicalClosure :=
    { SubringClass.toNormedRing S.topologicalClosure with
      mul_comm := (S.commRingTopologicalClosure hs').mul_comm }
  letI : CommCStarAlgebra S.topologicalClosure := { }
  set xc := StarSubalgebra.inclusion S.le_topologicalClosure ⟨x, hx⟩
  have h1 : ‖x‖ = ‖xc‖ := rfl
  rw [h1, ← (AddMonoidHomClass.isometry_iff_norm _).mp (gelfandTransform_isometry S.topologicalClosure) xc]
  refine (ContinuousMap.norm_le _ hc).2 fun φ => ?_
  have := h (WeakDual.CharacterSpace.equivAlgHom φ)
  rwa [WeakDual.CharacterSpace.equivAlgHom_coe] at this
end PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
