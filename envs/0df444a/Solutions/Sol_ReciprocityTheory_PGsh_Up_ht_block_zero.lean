-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.ht_block_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:42:11.335984+00:00
-- url     : https://prove2.me/submissions/1fee5c79-6479-45c8-8ce9-d356353db0a2

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MapSmulOneMulVec
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
import Theorems.Thm_ReciprocityTheory_PGsh_Up_htd_domain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (k j : Fin U.m) (hkj : U.cj k ≠ j) :
    (U.εL k)ᵀ * H.Ht * U.εT j = 0 := by
  haveI := htd_domain hS
  obtain ⟨a, ha⟩ := U.distinct (U.cj k) j hkj
  set X := (U.εL k)ᵀ * H.Ht * U.εT j with hX
  have h1 : (U.εL k)ᵀ * (H.ρL (σ a))ᵀ = U.sg (U.cj k) a • (U.εL k)ᵀ := by
    rw [← Matrix.transpose_mul, U.εL_eig, Matrix.transpose_smul, U.conj]
  have h2 : H.Ht * (H.ρ a).map (algebraMap ℤ_[p] R) * U.εT j = U.sg j a • (H.Ht * U.εT j) := by
    rw [Matrix.mul_assoc, U.εT_eig, Matrix.mul_smul]
  have h3 : U.sg j a • X = U.sg (U.cj k) a • X := by
    calc U.sg j a • X = (U.εL k)ᵀ * (H.Ht * (H.ρ a).map (algebraMap ℤ_[p] R) * U.εT j) := by
          rw [h2, Matrix.mul_smul, hX, Matrix.mul_assoc]
      _ = (U.εL k)ᵀ * ((H.ρL (σ a))ᵀ * H.Ht * U.εT j) := by rw [H.Ht_equivariant.1 a]
      _ = U.sg (U.cj k) a • X := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.smul_mul, Matrix.smul_mul, hX]
  have h4 : (U.sg (U.cj k) a - U.sg j a) • X = 0 := by rw [sub_smul, ← h3, sub_self]
  have hc : U.sg (U.cj k) a - U.sg j a ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at ha
    exact zero_ne_one ha
  ext i1 i2
  have h5 := congrFun (congrFun h4 i1) i2
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h5
  exact (mul_eq_zero.1 h5).resolve_left hc
end ReciprocityTheory.PGsh.Up
