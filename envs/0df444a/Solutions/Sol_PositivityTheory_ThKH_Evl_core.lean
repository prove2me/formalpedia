-- Prove2me | solution 1 for PositivityTheory.ThKH.Evl.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:34:51.56355+00:00
-- url     : https://prove2.me/submissions/03b533ea-5b0b-4b24-84a2-f74960fee88b

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IntegrablePair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_CyclicAndLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsEqMulApplyZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsInvariantForm
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DualNumberGraphFiltrationIsotropicOfSkew
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Theorems.Thm_PositivityTheory_ThKH_Evl_schr_schr
import Theorems.Thm_PositivityTheory_ThKH_Evl_schr_mem
import Theorems.Thm_PositivityTheory_ThKH_Evl_cyc

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
theorem _root_.solution (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1) (h1 : ψ ≠ 1) {φ₀ : (κ → k) → ℂ} (h₀ : φ₀ ∈ SB (κ → k)) (hne : φ₀ ≠ 0)
    (A : Set ((κ → k) × (κ → k))) (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (hA : ∀ a ∈ A, ∀ φ ∈ SB (κ → k), l (schr ψ a φ) = l φ)
    (hs : ∀ w, ∃ a ∈ A, ∃ b, w = a + b ∧ ((∃ c : ℂ, schr ψ b φ₀ = c • φ₀) ∨
      ∃ a' ∈ A, schr ψ a' φ₀ = φ₀ ∧ ψ (a'.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a'.2) ≠ 1))
    (hl : l φ₀ = 0) : ∀ φ ∈ SB (κ → k), l φ = 0 := by
  have hne0 : ∀ x, ψ x ≠ 0 := fun x h => by simpa [h] using hn x
  refine cyc hc hn h1 h₀ hne l fun w => ?_
  obtain ⟨a, ha, b, rfl, hb⟩ := hs w
  have e := hA a ha _ (schr_mem hc b h₀)
  rw [schr_schr, map_smul, smul_eq_mul] at e
  suffices h : l (schr ψ b φ₀) = 0 from (mul_eq_zero.1 (e.trans h)).resolve_left (hne0 _)
  rcases hb with ⟨c, hc'⟩ | ⟨a', ha', hfix, hψ⟩
  · rw [hc', map_smul, hl, smul_zero]
  · have e1 := hA a' ha' _ (schr_mem hc b h₀)
    rw [schr_schr, map_smul, smul_eq_mul] at e1
    have e2 : l (schr ψ b φ₀) = l (schr ψ b (schr ψ a' φ₀)) := by rw [hfix]
    rw [schr_schr, map_smul, smul_eq_mul, add_comm b a'] at e2
    set t := a'.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a'.2 with ht
    have e3 : ψ (⅟(2 : k) * t) = ψ t * ψ (⅟(2 : k) * (b.1 ⬝ᵥ a'.2 - a'.1 ⬝ᵥ b.2)) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      have h2 : ⅟(2 : k) * 2 = 1 := invOf_mul_self _
      rw [ht]
      linear_combination (a'.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a'.2) * h2
    rw [e3, mul_assoc, ← e2] at e1
    have : (ψ t - 1) * l (schr ψ b φ₀) = 0 := by linear_combination e1
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hψ)
end PositivityTheory.ThKH.Evl
