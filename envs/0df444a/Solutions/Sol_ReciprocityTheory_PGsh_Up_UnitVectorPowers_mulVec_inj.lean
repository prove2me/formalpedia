-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.UnitVectorPowers.mulVec_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:56:51.75245+00:00
-- url     : https://prove2.me/submissions/ba4ad5ab-14e3-44de-be96-34c35b430ba7

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_ProdPowUnitVectorVal
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_isUnit_det_MuR


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
theorem _root_.solution (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    {a b : Nb p g → R} (h : MuR hv D *ᵥ a = MuR hv D *ᵥ b) : a = b := by
  have h1 := congrArg (fun w => (MuR hv D)⁻¹ *ᵥ w) h
  simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_MuR hv hp1 D),
    Matrix.one_mulVec] using h1
end ReciprocityTheory.PGsh.Up.UnitVectorPowers
