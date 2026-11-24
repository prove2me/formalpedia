-- Prove2me | solution 1 for PositivityTheory.ThK.LinAct.lagY_dim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:55:22.342661+00:00
-- url     : https://prove2.me/submissions/e291197a-1d8f-4a5c-8c60-727004d68823

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_LagrangianStabilizerCharacterTrivial
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_LinearActAlg
import Theorems.Thm_PositivityTheory_ThK_LinAct_card_lagr
import Theorems.Thm_PositivityTheory_ThK_LinAct_indep

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
omit [DecidableEq α]
namespace PositivityTheory.ThK.LinAct
theorem _root_.solution [Nontrivial K] {ξ₀ : K} (hq : IsQuad c ξ₀) {ξ : K} {JA : Matrix α α K} {JB : Matrix β β K}
    (d : Darboux (symp (R := k) c ξ JB JA) κ) {Cy : Matrix β ν K} (h : IsLagr c JB Cy) :
    Module.finrank k (lagY d Cy) = Fintype.card κ := by
  obtain ⟨b, -, -⟩ := hq.basis
  have : Module.Free k K := Module.Free.of_basis b
  have : Module.Finite k K := Module.Finite.of_basis b
  have hK : Module.finrank k K = 2 := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hcard := card_lagr h
  obtain ⟨-, Cx, M, -, -, hM⟩ := h
  have hd := d.e.finrank_eq
  rw [Module.finrank_matrix, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hK, hcard] at hd
  unfold lagY
  rw [LinearMap.finrank_range_of_inj, Module.finrank_matrix, hK]
  · linarith
  · intro z z' hz
    have hz' : Cy * z = Cy * z' := d.e.injective hz
    have h3 : Cy * (z - z') + Cx * (0 : Matrix ν α K) = 0 := by
      rw [Matrix.mul_sub, hz', sub_self, Matrix.mul_zero, add_zero]
    exact sub_eq_zero.1 (indep hM h3).1
end PositivityTheory.ThK.LinAct
