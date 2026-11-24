-- Prove2me | solution 1 for PositivityTheory.ThK.LinAct.mem_lagY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:41:26.355315+00:00
-- url     : https://prove2.me/submissions/ab0f09e8-a2f4-4626-8ade-981890175b07

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
omit [DecidableEq α] [DecidableEq β] [DecidableEq ν]
namespace PositivityTheory.ThK.LinAct
theorem _root_.solution {ξ : K} {JA : Matrix α α K} {JB : Matrix β β K} {d : Darboux (symp (R := k) c ξ JB JA) κ} {Cy : Matrix β ν K}
    {w : (κ → k) × (κ → k)} : w ∈ lagY d Cy ↔ ∃ z : Matrix ν α K, d.e (Cy * z) = w := by
  simp [lagY, LinearMap.mem_range]
end PositivityTheory.ThK.LinAct
