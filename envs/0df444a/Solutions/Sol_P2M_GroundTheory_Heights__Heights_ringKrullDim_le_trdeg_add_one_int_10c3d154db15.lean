-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ringKrullDim_le_trdeg_add_one_int_10c3d154db15
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:00:05.535077+00:00
-- url     : https://prove2.me/submissions/d0084c8c-dfe6-4da6-a823-d69e47cc352a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IntDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IntDimBounds
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_le_add_one_of_quotient_le_783e1e3aab90
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_eq_trdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_trdeg_lt_of_surjective_of_ker_ne_bot_e46280f334dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_trdeg_zmod_quotient_le_1b4c4c03bf8d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Algebra Cardinal
open scoped TensorProduct
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (t : ℕ) : ∀ (B : Type) [CommRing B] [IsDomain B]
    [Algebra ℤ B] [Algebra.FiniteType ℤ B], Function.Injective (algebraMap ℤ B) →
    trdeg ℤ B = t → ringKrullDim B ≤ (((t + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro B _ _ _ _ hinj ht
  have hfin : trdeg ℤ B < ℵ₀ := by rw [ht]; exact Cardinal.natCast_lt_aleph0
  have key := ringKrullDim_le_add_one_of_quotient_le (B := B) (t : ℕ∞) (fun Q hQ hQ0 => by
    haveI := hQ
    haveI : Algebra.FiniteType ℤ (B ⧸ Q) :=
      .of_surjective (Ideal.Quotient.mkₐ ℤ Q) (Ideal.Quotient.mkₐ_surjective ℤ Q)
    by_cases hc : Function.Injective (algebraMap ℤ (B ⧸ Q))
    · have hlt := trdeg_lt_of_surjective_of_ker_ne_bot (Ideal.Quotient.mkₐ ℤ Q)
        (Ideal.Quotient.mkₐ_surjective ℤ Q)
        (fun h => hQ0 (by rw [← Ideal.mk_ker (I := Q)]; exact h)) hc hfin
      obtain ⟨t', ht'⟩ := Cardinal.lt_aleph0.mp (hlt.trans hfin)
      rw [ht, ht'] at hlt
      have hlt' : t' < t := by exact_mod_cast hlt
      refine (ih t' hlt' (B ⧸ Q) hc ht').trans ?_
      exact_mod_cast (show t' + 1 ≤ t by omega)
    · have hp0 : ringChar (B ⧸ Q) ≠ 0 := by
        intro h0
        have hc0 := ringChar.charP (B ⧸ Q)
        rw [h0] at hc0
        haveI : CharZero (B ⧸ Q) := (CharP.charP_zero_iff_charZero _).mp hc0
        apply hc
        have e : algebraMap ℤ (B ⧸ Q) = Int.castRingHom (B ⧸ Q) := RingHom.ext_int _ _
        rw [e]
        exact Int.cast_injective
      haveI : CharP (B ⧸ Q) (ringChar (B ⧸ Q)) := ringChar.charP _
      have hpp : (ringChar (B ⧸ Q)).Prime :=
        (CharP.char_is_prime_or_zero (B ⧸ Q) (ringChar (B ⧸ Q))).resolve_right hp0
      haveI : Fact (ringChar (B ⧸ Q)).Prime := ⟨hpp⟩
      letI := ZMod.algebra (B ⧸ Q) (ringChar (B ⧸ Q))
      haveI := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int (algebraMap ℤ (B ⧸ Q))
        ((algebraMap (ZMod (ringChar (B ⧸ Q))) (B ⧸ Q)).comp (algebraMap ℤ (ZMod (ringChar (B ⧸ Q))))))
      haveI : Algebra.FiniteType (ZMod (ringChar (B ⧸ Q))) (B ⧸ Q) :=
        Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _
      have hle := trdeg_zmod_quotient_le hinj (ringChar (B ⧸ Q)) Q
      rw [ht] at hle
      obtain ⟨s, hs⟩ := Cardinal.lt_aleph0.mp (hle.trans_lt Cardinal.natCast_lt_aleph0)
      rw [hs] at hle
      have hst : s ≤ t := by exact_mod_cast hle
      rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg (ZMod (ringChar (B ⧸ Q))), hs,
        Cardinal.toENat_nat]
      exact_mod_cast hst)
  refine key.trans (le_of_eq ?_)
  push_cast
  rfl
end GroundTheory.Heights₂.Heights
