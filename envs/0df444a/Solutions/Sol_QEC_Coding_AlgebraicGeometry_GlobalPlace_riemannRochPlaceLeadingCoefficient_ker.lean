-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochPlaceLeadingCoefficient_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:46:48.135408+00:00
-- url     : https://prove2.me/submissions/ee0b6a46-b4ee-4cef-8dfe-cde9efc07921

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PrincipalShift
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_residue_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_maximalIdeal_eq_span_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_mem_valuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_order_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residue_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    letI : Algebra k P.residueField := residueAlgebra P
    LinearMap.ker (riemannRochPlaceLeadingCoefficient G P) =
      riemannRochPlaceIncrementSubmodule G P := by
  letI : Algebra k P.residueField := residueAlgebra P
  ext x
  rw [LinearMap.mem_ker]
  change P.residue (riemannRochPlaceLeadingCoefficientValue G P x) = 0 ↔
    (x : F) ∈ riemannRochSubmodule G
  rw [P.residue_eq_zero_iff]
  constructor
  · intro hmaximal
    by_cases hx : (x : F) = 0
    · simpa only [hx] using (riemannRochSubmodule G).zero_mem
    · apply (mem_riemannRochSubmodule_iff_order_add_nonnegative G hx).mpr
      intro Q
      by_cases hQP : Q = P
      · subst Q
        rw [P.maximalIdeal_eq_span_uniformizer,
          Ideal.mem_span_singleton'] at hmaximal
        rcases hmaximal with ⟨r, hr⟩
        have hpi_ne : (P.uniformizerInValuationRing : F) ≠ 0 := by
          change P.uniformizer ≠ 0
          exact P.valuation.ne_zero_iff.mp (by
            rw [P.valuation_uniformizer]
            exact WithZero.exp_ne_zero)
        have hpi_order : P.order (P.uniformizerInValuationRing : F) = 1 := by
          change P.order P.uniformizer = 1
          exact P.order_uniformizer
        have hrF : (r : F) * (P.uniformizerInValuationRing : F) =
            Differential.localParameterPower P (G P + 1) * (x : F) := by
          exact congrArg (fun z : P.valuationRing => (z : F)) hr
        by_cases hr0 : (r : F) = 0
        · exfalso
          apply hx
          have hproduct :
              Differential.localParameterPower P (G P + 1) * (x : F) = 0 := by
            rw [← hrF, hr0, zero_mul]
          exact (mul_eq_zero.mp hproduct).resolve_left
            (localParameterPower_ne_zero P (G P + 1))
        · have hrOrder : 0 ≤ P.order (r : F) :=
            (regularAt_iff_order_nonnegative P hr0).mp
              ((regularAt_iff_mem_valuationRing P _).mpr r.property)
          have horder := congrArg P.order hrF
          rw [order_mul P hr0 hpi_ne,
            order_mul P (localParameterPower_ne_zero P (G P + 1)) hx,
            hpi_order, localParameterPower_order] at horder
          omega
      · have hxQ :=
          (mem_riemannRochSubmodule_iff_order_add_nonnegative
            (G + placeDivisor P) hx).mp x.property Q
        rw [Finsupp.add_apply,
          placeDivisor_apply_of_ne P Q (Ne.symm hQP), add_zero] at hxQ
        exact hxQ
  · intro hxG
    by_cases hx : (x : F) = 0
    · have hvalue : riemannRochPlaceLeadingCoefficientValue G P x = 0 := by
        apply Subtype.ext
        change Differential.localParameterPower P (G P + 1) * (x : F) = 0
        rw [hx, mul_zero]
      rw [hvalue]
      exact (IsLocalRing.maximalIdeal P.valuationRing).zero_mem
    · have hxOrder :=
        (mem_riemannRochSubmodule_iff_order_add_nonnegative G hx).mp hxG P
      let pi : P.valuationRing := P.uniformizerInValuationRing
      let t : F := Differential.localParameterPower P (G P + 1)
      let q : F := t * (x : F) * (pi : F)⁻¹
      have ht_ne : t ≠ 0 := localParameterPower_ne_zero P (G P + 1)
      have hpi_ne : (pi : F) ≠ 0 := by
        change P.uniformizer ≠ 0
        exact P.valuation.ne_zero_iff.mp (by
          rw [P.valuation_uniformizer]
          exact WithZero.exp_ne_zero)
      have hq_ne : q ≠ 0 :=
        mul_ne_zero (mul_ne_zero ht_ne hx) (inv_ne_zero hpi_ne)
      have hqOrder : 0 ≤ P.order q := by
        dsimp only [q]
        rw [order_mul P (mul_ne_zero ht_ne hx) (inv_ne_zero hpi_ne),
          order_mul P ht_ne hx, order_inv,
          show P.order (pi : F) = 1 by
            change P.order P.uniformizer = 1
            exact P.order_uniformizer,
          show P.order t = G P + 1 by
            exact localParameterPower_order P (G P + 1)]
        omega
      have hqmem : q ∈ P.valuationRing :=
        (regularAt_iff_mem_valuationRing P _).mp
          ((regularAt_iff_order_nonnegative P hq_ne).mpr hqOrder)
      rw [P.maximalIdeal_eq_span_uniformizer]
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨⟨q, hqmem⟩, ?_⟩
      apply Subtype.ext
      change q * (pi : F) = t * (x : F)
      simp only [q]
      field_simp [hpi_ne]
end QEC.Coding.AlgebraicGeometry.GlobalPlace
