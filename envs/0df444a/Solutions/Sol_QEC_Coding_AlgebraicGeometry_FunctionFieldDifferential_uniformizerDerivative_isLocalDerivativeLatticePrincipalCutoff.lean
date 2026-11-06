-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:27:28.70632+00:00
-- url     : https://prove2.me/submissions/c90da2f4-9be3-430e-87f2-238d37389fda

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalLogarithmicDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_localDerivativeLattice_eq_span_uniformizerDerivative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDerivation_uniformizer_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_mem_valuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_order_nonnegative


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution
    (P : GlobalPlace k F) :
    IsLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P
      (functionFieldDerivation (k := k) (F := F)
        (P.uniformizerInValuationRing : F)) := by
  let a : F := functionFieldDerivation (k := k) (F := F)
    (P.uniformizerInValuationRing : F)
  change IsLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P a
  have ha_ne : a ≠ 0 :=
    functionFieldDerivation_uniformizer_ne_zero (k := k) (F := F) P
  have hspan : localDerivativeLattice (k := k) (F := F) P =
      Submodule.span P.valuationRing ({a} : Set F) :=
    localDerivativeLattice_eq_span_uniformizerDerivative (k := k) (F := F) P
  refine ⟨ha_ne, hspan, ?_⟩
  intro x
  constructor
  · intro hx
    rw [hspan] at hx
    rcases Submodule.mem_span_singleton.mp hx with ⟨r, hr⟩
    by_cases hr0 : (r : F) = 0
    · left
      rw [← hr]
      change (r : F) * a = 0
      rw [hr0, zero_mul]
    · right
      have hr_order : 0 ≤ P.order (r : F) :=
        (GlobalPlace.regularAt_iff_order_nonnegative P hr0).mp
          ((GlobalPlace.regularAt_iff_mem_valuationRing P _).mpr r.property)
      have hx_order : P.order x = P.order (r : F) + P.order a := by
        rw [← hr]
        change P.order ((r : F) * a) = P.order (r : F) + P.order a
        exact GlobalPlace.order_mul P hr0 ha_ne
      omega
  · rintro (rfl | hx_order)
    · exact Submodule.zero_mem _
    · by_cases hx0 : x = 0
      · rw [hx0]
        exact Submodule.zero_mem _
      · rw [hspan]
        refine Submodule.mem_span_singleton.mpr ⟨⟨x * a⁻¹, ?_⟩, ?_⟩
        · apply (GlobalPlace.regularAt_iff_mem_valuationRing P _).mp
          apply (GlobalPlace.regularAt_iff_order_nonnegative P
            (mul_ne_zero hx0 (inv_ne_zero ha_ne))).mpr
          rw [GlobalPlace.order_mul P hx0 (inv_ne_zero ha_ne),
            GlobalPlace.order_inv]
          omega
        · change (x * a⁻¹) * a = x
          rw [mul_assoc, inv_mul_cancel₀ ha_ne, mul_one]
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
