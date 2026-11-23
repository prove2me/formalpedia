-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix.residue_p
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:54.798882+00:00
-- url     : https://prove2.me/submissions/d5014d1f-2fec-49f0-b8ae-ee51f0df8c30

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatementHolds
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_mem_max_of_lt

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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix
open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}
namespace ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix
theorem _root_.solution (hv : v.Integers R) [IsLocalRing R] (hp1 : v (algebraMap R C (p : R)) < 1) :
    ((p : ℕ) : IsLocalRing.ResidueField R) = 0 := by
  rw [← map_natCast (IsLocalRing.residue R) p, IsLocalRing.residue_eq_zero_iff]
  exact mem_max_of_lt hv hp1
end ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix
