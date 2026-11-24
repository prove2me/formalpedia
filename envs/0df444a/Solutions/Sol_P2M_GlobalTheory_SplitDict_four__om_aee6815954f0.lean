-- Prove2me | solution 1 for P2M_GlobalTheory_SplitDict_four__om_aee6815954f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:19:39.233335+00:00
-- url     : https://prove2.me/submissions/7b8863c6-0f8a-428d-9041-3342f16ebefb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBoxInvariantSnd
import Theorems.Thm_GlobalTheory_SplitDict_integral_shift
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GLMatrixJoining_glueCols_mul_uMat
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GLMatrixJoining_om_uGL


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
theorem _root_.solution (Φ : Matrix W (ρ ⊕ v ⊕ ρ) k → ℂ) (ν : Matrix v ρ k) (ν' : Matrix ρ v k) (b : Matrix ρ ρ k)
    (ξ : Matrix W ρ k) (η : Matrix ρ W k) (x₀ : Matrix W v k) :
    four₁ ψ m s₁ (om μ (uGL ν ν' b) 1 Φ) (ξ, η, x₀) =
      chr ψ s₁ (trace (η * (ξ * b + x₀ * ν))) * four₁ ψ m s₁ Φ (ξ, η, x₀ + ξ * ν') := by
  simp only [four₁, om_uGL, glueCols_mul_uMat, add_assoc]
  exact integral_shift ψ m s₁ (fun c => Φ (glueCols ξ (x₀ + ξ * ν') c)) (fun c => trace (η * c))
    (fun x y => by rw [Matrix.mul_add, Matrix.trace_add]) (ξ * b + x₀ * ν)
end GlobalTheory.SplitDict
