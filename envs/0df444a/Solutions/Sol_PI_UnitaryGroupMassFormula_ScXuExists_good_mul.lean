-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.good_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:17.378172+00:00
-- url     : https://prove2.me/submissions/0ee8f2c7-7c5c-42c9-bf66-2cdee1eb36b7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open Matrix
variable {K : Type} [Field K] (O : ValuationSubring K) {n r : ℕ} (P : Matrix (Fin n) (Fin n) K)
  (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K)
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution {S T : GL (Fin n) K} (hS : Good O P Λ1 Λ2 a a' α α' S)
    (hT : Good O P Λ1 Λ2 a a' α α' T) : Good O P Λ1 Λ2 a a' α α' (S * T) := by
  unfold Good at hS hT ⊢
  obtain ⟨hS1, hS2, hS3⟩ := hS
  obtain ⟨hT1, hT2, hT3⟩ := hT
  have hmul : ((S * T : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (S : Matrix (Fin n) (Fin n) K) * (T : Matrix (Fin n) (Fin n) K) := Units.val_mul S T
  have hinv : (((S * T)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((S⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [_root_.mul_inv_rev]
    exact Units.val_mul _ _
  rw [hinv, hmul]
  refine ⟨fun x hx => ?_, fun β hβ => ?_, fun i => ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(hS1 _ (hT1 x hx).1).1, (hT1 _ (hS1 x hx).2).2⟩
  · rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
    obtain ⟨⟨β1, hβ1, e1⟩, -⟩ := hS2 β hβ
    obtain ⟨⟨β2, hβ2, e2⟩, -⟩ := hT2 β1 hβ1
    obtain ⟨-, ⟨γ1, hγ1, f1⟩⟩ := hT2 β hβ
    obtain ⟨-, ⟨γ2, hγ2, f2⟩⟩ := hS2 γ1 hγ1
    exact ⟨⟨β2, hβ2, by rw [e2, e1]⟩, ⟨γ2, hγ2, by rw [f2, f1]⟩⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hS3 i
    obtain ⟨k1, k2, k3, k4⟩ := hT3 i
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
      k1, k2, h1, h2, h3, h4, k3, k4]
    exact ⟨rfl, rfl, rfl, rfl⟩
end PI.UnitaryGroupMassFormula.ScXuExists
