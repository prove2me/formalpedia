-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.UnitVectorPowers.u_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:49:06.304253+00:00
-- url     : https://prove2.me/submissions/0715618d-da1c-4288-bc21-d5e9b04cf3ae

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_ProdPowUnitVectorVal
import Theorems.Thm_ReciprocityTheory_PGsh_Up_UnitVectorPowers_red_mulVec
import Theorems.Thm_ReciprocityTheory_PGsh_Up_UnitVectorPowers_red_surj

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
theorem _root_.solution (D : Lifts H U X) (j : Ix g) (k : Fin D.s) (y : Nb p g) :
    D.u j (psi (H := H) (D.b k) y) = algebraMap R C (U.sg (D.κ j) (D.b k)) * D.u j y := by
  obtain ⟨t, rfl⟩ := red_surj y
  have h := D.eig j k t
  rw [red_mulVec] at h
  exact h
end ReciprocityTheory.PGsh.Up.UnitVectorPowers
