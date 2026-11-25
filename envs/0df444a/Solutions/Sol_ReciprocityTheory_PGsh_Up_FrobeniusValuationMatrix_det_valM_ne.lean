-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix.det_valM_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:57:08.188881+00:00
-- url     : https://prove2.me/submissions/4bc44399-6593-401b-98e1-bdb5f6fac263

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatementHolds
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_det_map__ae2c7b07d364
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_isUnit_det_MuR
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_valM_eq

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
theorem _root_.solution (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X) :
    (valM D).det ≠ 0 := by
  rw [valM_eq hv D, Matrix.det_mul, det_map', Matrix.det_diagonal]
  refine mul_ne_zero ((isUnit_det_MuR hv hp1 D).map (algebraMap R C)).ne_zero ?_
  refine Finset.prod_ne_zero_iff.mpr fun α _ => ?_
  rw [map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  rw [map_pow]
  exact pow_ne_zero _ ((map_ne_zero_iff _ hv.hom_inj).mpr (D.ε_ne j))
end ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix
