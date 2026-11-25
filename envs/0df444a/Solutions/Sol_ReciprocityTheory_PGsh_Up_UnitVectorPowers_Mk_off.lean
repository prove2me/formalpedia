-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.UnitVectorPowers.Mk_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:19:01.73983+00:00
-- url     : https://prove2.me/submissions/74b07b5e-c883-426c-aed0-3b8d2fb9c3e9

import Definitions.Def_ReciprocityTheory_DualLattices_ProdPowUnitVectorVal
import Definitions.Def_ReciprocityTheory_DualLattices_FormMonomialUnitVector
import Theorems.Thm_ReciprocityTheory_PGsh_Up_UnitVectorPowers_res_bR
import Theorems.Thm_ReciprocityTheory_PGsh_Up_UnitVectorPowers_bR_off


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
variable [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) p]
namespace ReciprocityTheory.PGsh.Up.UnitVectorPowers
theorem _root_.solution (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j l : Ix g) (hl : D.κ l ≠ U.φ (D.κ j)) : Mk D j l = 0 := by
  rw [← res_bR hv hp1 D j l, bR_off hv hp1 D j l hl, map_zero]
end ReciprocityTheory.PGsh.Up.UnitVectorPowers
