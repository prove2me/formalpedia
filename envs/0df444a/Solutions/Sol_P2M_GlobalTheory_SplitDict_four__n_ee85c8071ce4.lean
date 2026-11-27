-- Prove2me | solution 1 for P2M_GlobalTheory_SplitDict_four__n_ee85c8071ce4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:58:55.9333+00:00
-- url     : https://prove2.me/submissions/88b7c701-5757-4ec4-a42d-e90c0d27be05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBoxInvariantSnd
import Theorems.Thm_P2M_GlobalTheory_SplitDict_four__om_aee6815954f0
import Theorems.Thm_GlobalTheory_SplitDict_glueFun_mul_glueRows
import Theorems.Thm_GlobalTheory_SplitDict_glueRows_add_mul

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
theorem _root_.solution (Φ : Matrix (τ ⊕ w ⊕ τ) (ρ ⊕ v ⊕ ρ) k → ℂ) (ν : Matrix v ρ k) (ν' : Matrix ρ v k)
    (ξ' : Matrix τ ρ k) (ξ₀ : Matrix w ρ k) (η₀ : Matrix ρ w k) (ηd : Matrix ρ τ k)
    (r ys : Matrix τ v k) (x₀₀ : Matrix w v k) :
    four₁ ψ m s₁ (om μ (nGL ν ν') 1 Φ) (glueRows ξ' ξ₀ 0, glueFun 0 η₀ ηd, glueRows r x₀₀ ys) =
      chr ψ s₁ (trace ((η₀ * x₀₀ + ηd * ys) * ν)) *
        four₁ ψ m s₁ Φ (glueRows ξ' ξ₀ 0, glueFun 0 η₀ ηd, glueRows (r + ξ' * ν') (x₀₀ + ξ₀ * ν') ys) := by
  have := four₁_om ψ m μ s₁ Φ ν ν' 0 (glueRows ξ' ξ₀ 0) (glueFun 0 η₀ ηd) (glueRows r x₀₀ ys)
  rw [Matrix.mul_zero, zero_add, ← Matrix.mul_assoc, glueFun_mul_glueRows, Matrix.zero_mul, zero_add,
    glueRows_add_mul] at this
  exact this
end GlobalTheory.SplitDict
