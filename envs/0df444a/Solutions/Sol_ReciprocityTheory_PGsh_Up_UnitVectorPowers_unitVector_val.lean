-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.UnitVectorPowers.unitVector_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:34:35.068337+00:00
-- url     : https://prove2.me/submissions/66c4f01b-af17-40cc-932b-7a07060af2ef

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
theorem _root_.solution (l j : Ix g) : ((e1 (p := p) l) j).val = if j = l then 1 else 0 := by
  unfold e1
  by_cases h : j = l
  · subst h
    simp [ZMod.val_one]
  · simp [Pi.single_apply, h]
end ReciprocityTheory.PGsh.Up.UnitVectorPowers
