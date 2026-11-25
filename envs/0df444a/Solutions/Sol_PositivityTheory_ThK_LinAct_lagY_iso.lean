-- Prove2me | solution 1 for PositivityTheory.ThK.LinAct.lagY_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:03.358048+00:00
-- url     : https://prove2.me/submissions/50d57337-7552-414d-ba65-e9e85e6269d6

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_LagrangianStabilizerCharacterTrivial
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_LinearActAlg
import Theorems.Thm_PositivityTheory_ThK_LinAct_hTens_transpose
import Theorems.Thm_PositivityTheory_ThK_LinAct_mem_lagY
import Theorems.Thm_GlobalTheory_CompanionTheory_SplitUnique_hTens_eq_zero


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
theorem _root_.solution {ξ : K} {JA : Matrix α α K} {JB : Matrix β β K} (d : Darboux (symp (R := k) c ξ JB JA) κ) {Cy : Matrix β ν K}
    (h : Cyᵀ * JB * Cy.map c = 0) : ∀ w ∈ lagY d Cy, ∀ w' ∈ lagY d Cy, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2 := by
  intro w hw w' hw'
  obtain ⟨z, rfl⟩ := mem_lagY.1 hw
  obtain ⟨z', rfl⟩ := mem_lagY.1 hw'
  have h0 := d.form (Cy * z) (Cy * z')
  have hs : symp (R := k) c ξ JB JA (Cy * z) (Cy * z') = 0 := by
    unfold symp
    rw [hTens_transpose, transpose_mul, transpose_mul,
      GlobalTheory.CompanionTheory.SplitUnique.hTens_eq_zero c JA h zᵀ z'ᵀ, mul_zero, map_zero]
  rw [hs] at h0
  exact sub_eq_zero.1 h0.symm
end PositivityTheory.ThK.LinAct
