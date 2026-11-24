-- Prove2me | solution 1 for PositivityTheory.ThK.LinAct.indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:41:24.95847+00:00
-- url     : https://prove2.me/submissions/b51cedba-5656-49b3-a6cb-073ae3cea59d

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_LagrangianStabilizerCharacterTrivial
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_LinearActAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.LinAct
set_option linter.unusedSectionVars false
variable {k : Type} [Field k] [Invertible (2 : k)] {K : Type} [CommRing K] [Algebra k K] {c : K →ₐ[k] K}
  {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
omit [Invertible (2 : k)] [Fintype α] [DecidableEq α]
namespace PositivityTheory.ThK.LinAct
theorem _root_.solution {Cy Cx : Matrix β ν K} {M : Matrix (ν ⊕ ν) β K} (h2 : M * fromCols Cy Cx = 1) {z z' : Matrix ν α K}
    (h : Cy * z + Cx * z' = 0) : z = 0 ∧ z' = 0 := by
  have hrows : fromRows z z' = 0 := by
    calc fromRows z z' = (M * fromCols Cy Cx) * fromRows z z' := by rw [h2, Matrix.one_mul]
      _ = M * (Cy * z + Cx * z') := by rw [Matrix.mul_assoc, fromCols_mul_fromRows]
      _ = 0 := by rw [h, Matrix.mul_zero]
  have e1 := congrArg Matrix.toRows₁ hrows
  have e2 := congrArg Matrix.toRows₂ hrows
  simp only [toRows₁_fromRows, toRows₂_fromRows] at e1 e2
  refine ⟨e1.trans ?_, e2.trans ?_⟩ <;> rfl
end PositivityTheory.ThK.LinAct
