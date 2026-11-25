-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.phi_x_grade
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:58:36.625795+00:00
-- url     : https://prove2.me/submissions/ce36c800-8040-4dd3-851f-24d8c4ce0a74

import Definitions.Def_ReciprocityTheory_DualLattices_HasLenLeOfSurj
import Definitions.Def_ReciprocityTheory_DualLattices_MulVecMemPP
import Theorems.Thm_ReciprocityTheory_PGsh_Up_mulVec_mem_pP
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_Up__L_eq_zero_of_r_a5bd42719c11
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3


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
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hS : HodgeTateSetting p v R O σ cp) (D : Lifts H U X) (k : Ix g) (τ : Fin U.m)
    (hτ : τ ≠ D.κ k) (l : Fin g → R)
    (hl : H.φ ⟨xL D k, D.x_mem k⟩ = Submodule.Quotient.mk l) :
    (U.εL τ)ᵀ *ᵥ l ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin g → R)) := by
  by_cases hτκ : ∃ j, D.κ j = τ
  · obtain ⟨j', rfl⟩ := hτκ
    obtain ⟨k', hk'⟩ := D.sep j' k hτ
    have hf' : ∀ t, ((U.sg (D.κ k) (D.b k') • (⟨xL D k, D.x_mem k⟩ : augIdeal H.AA.carrier) :
        augIdeal H.AA.carrier) : Nb p g → C) (red p g t) =
        ((⟨xL D k, D.x_mem k⟩ : augIdeal H.AA.carrier) : Nb p g → C) (red p g (H.ρ (D.b k') *ᵥ t)) := by
      intro t
      simp only [Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def, xL]
      rw [D.eig k k' t]
      ring
    have h1 := H.cotangent_linear (D.b k') _ _ l hf' hl
    rw [map_smul, hl, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at h1
    have h2 := mulVec_mem_pP (U.εL (D.κ j'))ᵀ h1
    have e : (U.εL (D.κ j'))ᵀ *ᵥ (U.sg (D.κ k) (D.b k') • l - (H.ρL (D.b k'))ᵀ *ᵥ l) =
        (U.sg (D.κ k) (D.b k') - U.sg (D.κ j') (D.b k')) • ((U.εL (D.κ j'))ᵀ *ᵥ l) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, U.εL_eig,
        Matrix.transpose_smul, Matrix.smul_mulVec, sub_smul]
    rw [e] at h2
    have hv : v (algebraMap R C (U.sg (D.κ k) (D.b k') - U.sg (D.κ j') (D.b k'))) = 1 := by
      rw [← neg_sub, map_neg, Valuation.map_neg]
      exact hk'
    have hunit : IsUnit (U.sg (D.κ k) (D.b k') - U.sg (D.κ j') (D.b k')) := by
      refine hS.integers.isUnit_of_one ?_ hv
      exact Ne.isUnit fun h0 => by rw [h0, Valuation.map_zero] at hv; exact zero_ne_one hv
    obtain ⟨u, hu⟩ := hunit
    have h3 := Submodule.smul_mem _ (↑u⁻¹ : R) h2
    rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h3
  · push_neg at hτκ
    rw [εL_eq_zero_of_r U (D.r_zero τ hτκ), Matrix.transpose_zero, Matrix.zero_mulVec]
    exact Submodule.zero_mem _
end ReciprocityTheory.PGsh.Up
