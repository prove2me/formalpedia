-- Prove2me | solution 1 for PositivityTheory.ThK.LinAct.card_lagr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:41:24.316276+00:00
-- url     : https://prove2.me/submissions/1d229df9-3c7c-45ca-8aaa-0507a883cf23

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
omit [Invertible (2 : k)]
namespace PositivityTheory.ThK.LinAct
theorem _root_.solution [Nontrivial K] {JB : Matrix β β K} {Cy : Matrix β ν K} (h : IsLagr c JB Cy) :
    Fintype.card β = 2 * Fintype.card ν := by
  obtain ⟨-, Cx, M, -, h1, h2⟩ := h
  let f : (β → K) ≃ₗ[K] (ν ⊕ ν → K) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' M) (Matrix.toLin' (fromCols Cy Cx))
      (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one])
  rw [card_eq_of_linearEquiv K f, Fintype.card_sum, two_mul]
end PositivityTheory.ThK.LinAct
