-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix.residue_uR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:53.435059+00:00
-- url     : https://prove2.me/submissions/15b9e5d9-efe1-485d-99f6-4b9f3f7abd4e

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatementHolds
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_uR_spec
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
theorem _root_.solution (hv : v.Integers R) [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) p]
    (D : Lifts H U X) (j : Ix g) (y : Nb p g) :
    IsLocalRing.residue R (uR hv D j y) = lam (D.Λ.map (IsLocalRing.residue R)) j y := by
  have h := D.u_cong j y
  rw [← uR_spec hv D j y, ← map_sub] at h
  have hm := mem_max_of_lt hv h
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hm
  rw [hm, lam]
  simp only [map_sum, map_mul, map_natCast, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [xc, ZMod.castHom_apply, ZMod.natCast_val]
end ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix
