-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.thetaQ_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:58:38.173618+00:00
-- url     : https://prove2.me/submissions/afc2f866-f93b-48e0-aa4e-356418ede8cb

import Definitions.Def_ReciprocityTheory_DualLattices_MulVecMemPP
import Definitions.Def_ReciprocityTheory_DualLattices_ThetaQSurj
import Theorems.Thm_ReciprocityTheory_PGsh_Up_theta_surj

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
    Function.Surjective (thetaQ U τ) := by
  intro y
  choose y' hy' using fun s => Submodule.mkQ_surjective (Ideal.span {(p : R)}) (y s)
  obtain ⟨l, hl⟩ := theta_surj U τ y'
  refine ⟨Submodule.Quotient.mk l, ?_⟩
  show redP (p := p) (U.r τ) (thetaL U τ l) = y
  rw [hl]
  funext s
  exact hy' s
end ReciprocityTheory.PGsh.Up
