-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.UnitVectorPowers.lam_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:34:27.799626+00:00
-- url     : https://prove2.me/submissions/423441ab-2805-4eb8-917f-1793e392a964

import Definitions.Def_ReciprocityTheory_DualLattices_ProdPowUnitVectorVal
import Definitions.Def_ReciprocityTheory_DualLattices_FormMonomialUnitVector
import Theorems.Thm_ReciprocityTheory_PGsh_Up_UnitVectorPowers_Lk_det

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
theorem _root_.solution (D : Lifts H U X) (j : Ix g) (y : Nb p g) :
    lam (Lk D) j y ^ p = ∑ l, Mk D j l * lam (Lk D) l y := by
  have hinv : (Lk D)⁻¹ * Lk D = 1 := Matrix.nonsing_inv_mul _ (Lk_det D)
  have hxc : ∀ i, (xc (IsLocalRing.ResidueField R) i y) ^ p = xc (IsLocalRing.ResidueField R) i y := by
    intro i
    simp only [xc]
    rw [← map_pow, ZMod.pow_card]
  have hR : ∑ l, Mk D j l * lam (Lk D) l y =
      ((Mk D * Lk D) *ᵥ fun i => xc (IsLocalRing.ResidueField R) i y) j := by
    rw [← Matrix.mulVec_mulVec]
    simp [Matrix.mulVec, dotProduct, lam]
  rw [hR]
  unfold Mk
  rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
  simp only [lam, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [sum_pow_char]
  simp only [mul_pow, hxc]
end ReciprocityTheory.PGsh.Up.UnitVectorPowers
