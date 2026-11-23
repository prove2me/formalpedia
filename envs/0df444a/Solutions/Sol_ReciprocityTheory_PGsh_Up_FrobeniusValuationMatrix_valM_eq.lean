-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix.valM_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:54.577203+00:00
-- url     : https://prove2.me/submissions/56b9e36a-a0f5-41bc-9eaa-4b40415f8d6c

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatementHolds
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_uR_spec

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
theorem _root_.solution (hv : v.Integers R) (D : Lifts H U X) :
    valM D = (MuR hv D).map (algebraMap R C) *
      Matrix.diagonal fun α : Nb p g => algebraMap R C (∏ j, D.ε j ^ (α j).val) := by
  ext y α
  simp only [valM, monX, xL, MuR, Matrix.of_apply, Matrix.mul_diagonal, Matrix.map_apply,
    map_prod, map_pow, uR_spec, mul_pow, Finset.prod_mul_distrib]
  ring
end ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix
