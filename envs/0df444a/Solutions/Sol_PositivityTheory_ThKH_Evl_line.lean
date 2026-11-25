-- Prove2me | solution 1 for PositivityTheory.ThKH.Evl.line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:17:38.936958+00:00
-- url     : https://prove2.me/submissions/4c8da002-8d19-4bd0-928e-4f130836acfa

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IntegrablePair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_CyclicAndLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsEqMulApplyZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsInvariantForm
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DualNumberGraphFiltrationIsotropicOfSkew
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Theorems.Thm_PositivityTheory_ThKH_Evl_exists_test

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM MeasureTheory
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Evl
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {κ : Type} [Fintype κ] {ψ : AddChar k ℂ}
namespace PositivityTheory.ThKH.Evl
theorem _root_.solution (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1) (h1 : ψ ≠ 1) (large₂ : Submodule k ((κ → k) × (κ → k)))
    (hiso : ∀ w ∈ large₂, ∀ w' ∈ large₂, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (hdim : Module.finrank k large₂ = Fintype.card κ)
    (l l' : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ w ∈ large₂, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ)
    (hl' : ∀ w ∈ large₂, ∀ φ ∈ SB (κ → k), l' (schr ψ w φ) = l' φ) (hne : ∃ φ ∈ SB (κ → k), l φ ≠ 0) :
    ∃ c : ℂ, ∀ φ ∈ SB (κ → k), l' φ = c * l φ := by
  obtain ⟨φ₀, h⟩ := exists_test hc hn h1 large₂ hiso hdim
  obtain ⟨φ₁, hφ₁, h₁⟩ := hne
  have h0 : l φ₀ ≠ 0 := fun e => h₁ (h l hl e φ₁ hφ₁)
  refine ⟨l' φ₀ / l φ₀, fun φ hφ => ?_⟩
  have := h (l' - (l' φ₀ / l φ₀) • l) (fun w hw φ hφ => by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, hl w hw φ hφ, hl' w hw φ hφ]) (by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h0, sub_self]) φ hφ
  simpa only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, sub_eq_zero] using this
end PositivityTheory.ThKH.Evl
