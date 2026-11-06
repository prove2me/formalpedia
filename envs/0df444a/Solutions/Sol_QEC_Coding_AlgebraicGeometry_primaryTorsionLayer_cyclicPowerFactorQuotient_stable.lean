-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionLayer_cyclicPowerFactorQuotient_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:27:34.533949+00:00
-- url     : https://prove2.me/submissions/7d43a10a-b87d-4757-ba02-772f85c49874

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PolynomialQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicTraceStabilization
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionLayer_mono
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation



set_option autoImplicit false
open scoped Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (q : R) (hq : Prime q) (e : ℕ) (b : R) (hb : ¬ q ∣ b)
    (j : ℕ) (hej : e ≤ j) :
    primaryTorsionLayer (Ideal.span {q})
        (R ⧸ Ideal.span {q ^ e * b}) j =
      primaryTorsionLayer (Ideal.span {q})
        (R ⧸ Ideal.span {q ^ e * b}) e := by
  apply le_antisymm
  · intro x hx
    rw [primaryTorsionLayer, Ideal.span_singleton_pow,
      Submodule.torsionBySet_ideal_span_singleton_eq,
      Submodule.mem_torsionBy_iff] at hx ⊢
    induction x using Quotient.inductionOn' with
    | _ r =>
        change Ideal.Quotient.mk (Ideal.span {q ^ e * b}) (q ^ j * r) = 0 at hx
        change Ideal.Quotient.mk (Ideal.span {q ^ e * b}) (q ^ e * r) = 0
        rw [Ideal.Quotient.eq_zero_iff_dvd] at hx ⊢
        obtain ⟨c, hc⟩ := hx
        have hpow : q ^ j = q ^ e * q ^ (j - e) := by
          rw [← pow_add, Nat.add_sub_of_le hej]
        have hcancel : q ^ (j - e) * r = b * c := by
          apply mul_left_cancel₀ (pow_ne_zero e hq.ne_zero)
          simpa only [hpow, mul_assoc] using hc
        have hcop : IsCoprime b (q ^ (j - e)) :=
          (hq.coprime_iff_not_dvd.mpr hb).symm.pow_right
        have hbdiv : b ∣ r :=
          hcop.dvd_of_dvd_mul_left ⟨c, hcancel⟩
        obtain ⟨d, hd⟩ := hbdiv
        refine ⟨d, ?_⟩
        rw [hd]
        ring
  · exact primaryTorsionLayer_mono (Ideal.span {q}) e j hej
end QEC.Coding.AlgebraicGeometry
