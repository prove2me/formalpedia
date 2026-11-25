-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.UnitVectorPowers.linX_xp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:06:01.951954+00:00
-- url     : https://prove2.me/submissions/358744c9-88da-4160-ac98-e14e67415b98

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_ProdPowUnitVectorVal
import Theorems.Thm_ReciprocityTheory_PGsh_Up_UnitVectorPowers_liftScalePow_unitVector
import Theorems.Thm_ReciprocityTheory_PGsh_Up_UnitVectorPowers_MuR_mulVec_bR
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_det_valM_ne
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_uR_spec
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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.UnitVectorPowers
open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}
namespace ReciprocityTheory.PGsh.Up.UnitVectorPowers
theorem _root_.solution (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j l : Ix g) :
    linX D (fun y => xL D j y ^ p) l =
      algebraMap R C (bR hv D j (e1 l)) * (algebraMap R C (D.ε j) ^ p / algebraMap R C (D.ε l)) := by
  have hdet := det_valM_ne hv hp1 D
  have hE : ∀ α, algebraMap R C (epow D α) ≠ 0 := by
    intro α
    simp only [epow, map_prod, map_pow]
    exact Finset.prod_ne_zero_iff.mpr fun j _ =>
      pow_ne_zero _ (fun h0 => D.ε_ne j (hv.hom_inj (h0.trans (map_zero _).symm)))
  have hf : (fun y => xL D j y ^ p) = valM D *ᵥ (fun α => algebraMap R C (D.ε j) ^ p *
      algebraMap R C (bR hv D j α) / algebraMap R C (epow D α)) := by
    funext y
    simp only [Matrix.mulVec, dotProduct, valM_eq hv D, Matrix.mul_diagonal, Matrix.map_apply]
    have h2 := congrFun (MuR_mulVec_bR hv hp1 D j) y
    simp only [Matrix.mulVec, dotProduct, hvec] at h2
    have h3 := congrArg (algebraMap R C) h2
    rw [map_sum, map_pow, uR_spec] at h3
    simp only [map_mul] at h3
    rw [xL, mul_pow, ← h3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    have h4 := hE α
    simp only [epow] at h4 ⊢
    field_simp
  unfold linX coefX
  rw [hf, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]
  show algebraMap R C (D.ε j) ^ p * algebraMap R C (bR hv D j (e1 l)) /
    algebraMap R C (epow D (e1 l)) = _
  rw [liftScalePow_unitVector]
  ring
end ReciprocityTheory.PGsh.Up.UnitVectorPowers
