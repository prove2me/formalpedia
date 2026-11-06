-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.isFullConstantField_of_rationalPlace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:48:10.051803+00:00
-- url     : https://prove2.me/submissions/d4f18058-1164-4b75-8d90-d7afbe592b7f

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_FullConstantField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Mathlib.FieldTheory.Finite.Valuation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceFullConstants
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    (Q : RationalPlace k F) : IsFullConstantField k F := by
  refine ⟨fun x hx => ?_⟩
  let E : IntermediateField k F := IntermediateField.adjoin k {x}
  letI : FiniteDimensional k E := IntermediateField.adjoin.finiteDimensional hx.isIntegral
  letI : Finite E := Module.finite_of_finite k
  let integralInclusion : E →+* Q.place.valuationRing :=
    (algebraMap E F).codRestrict Q.place.valuationRing fun y =>
      (GlobalPlace.mem_valuationRing_iff Q.place _).mpr
        (FiniteField.valuation_algebraMap_le_one Q.place.valuation y)
  let evaluateAdjoin : E →+* k := Q.evaluate.comp integralInclusion
  letI : Fintype k := Fintype.ofFinite k
  letI : Fintype E := Fintype.ofFinite E
  have hEk : Fintype.card E ≤ Fintype.card k :=
    Fintype.card_le_of_injective evaluateAdjoin evaluateAdjoin.injective
  have hkE : Fintype.card k ≤ Fintype.card E :=
    Fintype.card_le_of_injective (algebraMap k E) (algebraMap k E).injective
  have hcard : Fintype.card k = Fintype.card E := Nat.le_antisymm hkE hEk
  have hsurjective : Function.Surjective (algebraMap k E) :=
    ((Fintype.bijective_iff_injective_and_card (algebraMap k E)).mpr
      ⟨(algebraMap k E).injective, hcard⟩).2
  have hxmem : x ∈ E := IntermediateField.subset_adjoin k ({x} : Set F) (by simp)
  obtain ⟨c, hc⟩ := hsurjective ⟨x, hxmem⟩
  refine ⟨c, ?_⟩
  have hc' := congrArg (fun y : E => (y : F)) hc
  simpa [E] using hc'.symm
end QEC.Coding.AlgebraicGeometry
