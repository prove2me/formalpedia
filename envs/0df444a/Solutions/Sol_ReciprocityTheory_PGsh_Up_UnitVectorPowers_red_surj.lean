-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.UnitVectorPowers.red_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:34:31.775065+00:00
-- url     : https://prove2.me/submissions/914fd90e-d336-4c11-b424-6dbb4d724e54

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_ProdPowUnitVectorVal

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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.UnitVectorPowers
open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}
namespace ReciprocityTheory.PGsh.Up.UnitVectorPowers
theorem _root_.solution (y : Nb p g) : ∃ t : TT p g, red p g t = y := by
  exact ⟨fun i => ((y i).val : ℤ_[p]), funext fun i => by simp [red]⟩
end ReciprocityTheory.PGsh.Up.UnitVectorPowers
