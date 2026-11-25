-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.theta_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:48:19.567385+00:00
-- url     : https://prove2.me/submissions/92ad7974-c00b-4698-8e19-e426184b9884

import Definitions.Def_ReciprocityTheory_DualLattices_MulVecMemPP
import Definitions.Def_ReciprocityTheory_DualLattices_ThetaQSurj

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
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (U : UnramData p g v R O σ cp H) (τ : Fin U.m) :
    Function.Surjective (thetaL U τ) := by
  intro y
  classical
  have key : ∀ (φ : (Fin g → R) →ₗ[R] R) (z : Fin g → R),
      (fun i => φ (fun j => if i = j then 1 else 0)) ⬝ᵥ z = φ z := by
    intro φ z
    rw [LinearMap.pi_apply_eq_sum_univ φ z, dotProduct]
    exact Finset.sum_congr rfl fun i _ => by simp only [smul_eq_mul]; exact mul_comm _ _
  refine ⟨fun i => ((∑ s, y s • LinearMap.proj s : (Fin (U.r τ) → R) →ₗ[R] R) ∘ₗ
      (U.rank τ).some.toLinearMap ∘ₗ (Matrix.mulVecLin (U.εL τ)).rangeRestrict)
      (fun j => if i = j then 1 else 0), ?_⟩
  funext s
  show _ ⬝ᵥ bvec U τ s = y s
  refine (key _ _).trans ?_
  obtain ⟨x, hx⟩ := LinearMap.mem_range.1 ((U.rank τ).some.symm (Pi.single s 1)).2
  have hb : bvec U τ s = U.εL τ *ᵥ x := hx.symm
  have hfix : (Matrix.mulVecLin (U.εL τ)).rangeRestrict (bvec U τ s) =
      (U.rank τ).some.symm (Pi.single s 1) := by
    apply Subtype.ext
    show U.εL τ *ᵥ bvec U τ s = bvec U τ s
    rw [hb, mulVec_mulVec, U.εL_orth, if_pos rfl]
  simp only [LinearMap.comp_apply, hfix, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  simp [Pi.single_apply]
end ReciprocityTheory.PGsh.Up
