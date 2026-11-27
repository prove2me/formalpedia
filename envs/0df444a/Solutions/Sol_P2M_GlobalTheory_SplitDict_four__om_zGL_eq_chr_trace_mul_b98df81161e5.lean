-- Prove2me | solution 1 for P2M_GlobalTheory_SplitDict_four__om_zGL_eq_chr_trace_mul_b98df81161e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:53:31.949445+00:00
-- url     : https://prove2.me/submissions/98aebd54-b9b1-427f-b28e-57e0aefd46cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBoxInvariantSnd
import Theorems.Thm_P2M_GlobalTheory_SplitDict_four__om_aee6815954f0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitDict
variable {k : Type} [Field k]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable (ψ : AddChar k Circle) (m : Measure k) [m.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (s₁ s₂ : ℤˣ)
variable {ρ v τ w W : Type} [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v]
  [Fintype τ] [DecidableEq τ] [Fintype w] [DecidableEq w] [Fintype W] [DecidableEq W]
namespace GlobalTheory.SplitDict
theorem _root_.solution (Φ : Matrix W (ρ ⊕ v ⊕ ρ) k → ℂ) (b : Matrix ρ ρ k)
    (ξ : Matrix W ρ k) (η : Matrix ρ W k) (x₀ : Matrix W v k) :
    four₁ ψ m s₁ (om μ (zGL v b) 1 Φ) (ξ, η, x₀) =
      chr ψ s₁ (∑ p, ∑ q, (η * ξ) p q * b q p) * four₁ ψ m s₁ Φ (ξ, η, x₀) := by
  have := four₁_om ψ m μ s₁ Φ (0 : Matrix v ρ k) 0 b ξ η x₀
  simp only [Matrix.mul_zero, add_zero] at this
  rw [← Matrix.mul_assoc] at this
  show four₁ ψ m s₁ (om μ (uGL (0 : Matrix v ρ k) 0 b) 1 Φ) (ξ, η, x₀) = _
  rw [this, show trace (η * ξ * b) = ∑ p, ∑ q, (η * ξ) p q * b q p by
    simp [Matrix.trace, Matrix.mul_apply]]
end GlobalTheory.SplitDict
