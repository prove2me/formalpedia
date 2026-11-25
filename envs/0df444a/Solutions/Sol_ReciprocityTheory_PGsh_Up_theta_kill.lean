-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.theta_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:48:28.171747+00:00
-- url     : https://prove2.me/submissions/d4af953b-07bd-4e3b-8b68-a06f7e9b65b9

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
theorem _root_.solution (U : UnramData p g v R O σ cp H) {τ σ' : Fin U.m} (h : σ' ≠ τ) (μ : Fin g → R) :
    thetaL U τ ((U.εL σ')ᵀ *ᵥ μ) = 0 := by
  funext s
  obtain ⟨x, hx⟩ := LinearMap.mem_range.1 ((U.rank τ).some.symm (Pi.single s 1)).2
  have hb : bvec U τ s = U.εL τ *ᵥ x := hx.symm
  show ((U.εL σ')ᵀ *ᵥ μ) ⬝ᵥ bvec U τ s = 0
  rw [hb, mulVec_transpose, dotProduct_mulVec, vecMul_vecMul, U.εL_orth, if_neg h,
    vecMul_zero, zero_dotProduct]
end ReciprocityTheory.PGsh.Up
