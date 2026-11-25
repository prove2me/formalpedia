-- Prove2me | solution 1 for PositivityTheory.ThK.LinAct.schr_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:57.935115+00:00
-- url     : https://prove2.me/submissions/35a966e6-43a9-4bbe-aa33-2bfdbcffef69

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
omit [DecidableEq α] [DecidableEq β]
namespace PositivityTheory.ThK.LinAct
theorem _root_.solution (ψ : AddChar k ℂ) {κ' : Type} [Fintype κ'] (w : (κ ⊕ κ' → k) × (κ ⊕ κ' → k)) (φ₁ : (κ → k) → ℂ)
    (φ₂ : (κ' → k) → ℂ) : schr ψ w (boxFun φ₁ φ₂) =
      boxFun (schr ψ (w.1 ∘ Sum.inl, w.2 ∘ Sum.inl) φ₁) (schr ψ (w.1 ∘ Sum.inr, w.2 ∘ Sum.inr) φ₂) := by
  funext x
  have hd : ∀ u v : κ ⊕ κ' → k,
      u ⬝ᵥ v = (u ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inl) + (u ∘ Sum.inr) ⬝ᵥ (v ∘ Sum.inr) := fun u v => by
    simp [dotProduct, Fintype.sum_sum_type]
  have e1 : (x + w.1) ∘ Sum.inl = x ∘ Sum.inl + w.1 ∘ Sum.inl := rfl
  have e2 : (x + w.1) ∘ Sum.inr = x ∘ Sum.inr + w.1 ∘ Sum.inr := rfl
  simp only [schr, boxFun]
  rw [e1, e2, hd x w.2, hd w.1 w.2]
  have e3 : (x ∘ Sum.inl) ⬝ᵥ (w.2 ∘ Sum.inl) + (x ∘ Sum.inr) ⬝ᵥ (w.2 ∘ Sum.inr) +
      ⅟(2 : k) * ((w.1 ∘ Sum.inl) ⬝ᵥ (w.2 ∘ Sum.inl) + (w.1 ∘ Sum.inr) ⬝ᵥ (w.2 ∘ Sum.inr)) =
      ((x ∘ Sum.inl) ⬝ᵥ (w.2 ∘ Sum.inl) + ⅟(2 : k) * ((w.1 ∘ Sum.inl) ⬝ᵥ (w.2 ∘ Sum.inl))) +
      ((x ∘ Sum.inr) ⬝ᵥ (w.2 ∘ Sum.inr) + ⅟(2 : k) * ((w.1 ∘ Sum.inr) ⬝ᵥ (w.2 ∘ Sum.inr))) := by ring
  rw [e3, AddChar.map_add_eq_mul]
  ring
end PositivityTheory.ThK.LinAct
