-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport.simplePoleTraceResidue_rationalDifferentialInvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:46:02.977149+00:00
-- url     : https://prove2.me/submissions/6570a2f2-950e-4951-8773-ada633de5ea6

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_RationalInfinityTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueCoordinate
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InvolutionResidueTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseRationalInfinityTransport_rationalDifferentialInvolution_differential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseRationalInfinityTransport_rationalDifferentialInvolution_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleDifferential_eq_residueCoordinate_smul_uniformizerLogDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_eq_residueCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_logarithmicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseRationalInfinityTransport_xAdic_order_rationalInvolution_eq_rationalInfinity_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
namespace QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
open scoped Polynomial RatFunc WithZero
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
omit [Finite k] in
private theorem rationalDifferentialInvolution_logarithmicDifferential
    (f : RatFunc k) :
    rationalDifferentialInvolution (k := k)
        (Differential.logarithmicDifferential (k := k) (F := RatFunc k) f) =
      Differential.logarithmicDifferential (k := k) (F := RatFunc k)
        (InverseAffinePlace.rationalInvolution k f) := by
  rw [Differential.logarithmicDifferential,
    rationalDifferentialInvolution_smul,
    rationalDifferentialInvolution_differential, map_inv₀]
  rfl
@[simp]
private theorem rationalInfinityResidueEquivXAdic_residue
    (z : (GlobalPlace.rationalInfinity k).valuationRing) :
    rationalInfinityResidueEquivXAdic (k := k)
        ((GlobalPlace.rationalInfinity k).residue z) =
      (xAdicPlace k).residue
        (rationalInfinityValuationRingEquivXAdic (k := k) z) := by
  unfold rationalInfinityResidueEquivXAdic
  exact IsLocalRing.ResidueField.map_residue
    (rationalInfinityValuationRingEquivXAdic (k := k)).toRingHom z
private theorem rationalInfinityResidueEquivXAdic_constants (c : k) :
    rationalInfinityResidueEquivXAdic (k := k)
        (GlobalPlace.constantsToResidue (GlobalPlace.rationalInfinity k) c) =
      GlobalPlace.constantsToResidue (xAdicPlace k) c := by
  rw [show GlobalPlace.constantsToResidue (GlobalPlace.rationalInfinity k) c =
      (GlobalPlace.rationalInfinity k).residue
        (GlobalPlace.constantsToValuationRing
          (GlobalPlace.rationalInfinity k) c) from rfl,
    rationalInfinityResidueEquivXAdic_residue]
  apply congrArg (GlobalPlace.residue (xAdicPlace k))
  apply Subtype.ext
  change InverseAffinePlace.rationalInvolution k
      (algebraMap k (RatFunc k) c) = algebraMap k (RatFunc k) c
  exact (InverseAffinePlace.rationalInvolution k).commutes c
private theorem trace_rationalInfinityResidueEquivXAdic
    (z : (GlobalPlace.rationalInfinity k).residueField) :
    letI : Algebra k (GlobalPlace.rationalInfinity k).residueField :=
      GlobalPlace.residueAlgebra (GlobalPlace.rationalInfinity k)
    letI : Algebra k (xAdicPlace k).residueField :=
      GlobalPlace.residueAlgebra (xAdicPlace k)
    Algebra.trace k (xAdicPlace k).residueField
        (rationalInfinityResidueEquivXAdic (k := k) z) =
      Algebra.trace k (GlobalPlace.rationalInfinity k).residueField z := by
  letI : Algebra k (GlobalPlace.rationalInfinity k).residueField :=
    GlobalPlace.residueAlgebra (GlobalPlace.rationalInfinity k)
  letI : Algebra k (xAdicPlace k).residueField :=
    GlobalPlace.residueAlgebra (xAdicPlace k)
  let e := rationalInfinityResidueEquivXAdic (k := k)
  have he : RingHom.comp (algebraMap k (xAdicPlace k).residueField)
      (RingEquiv.refl k) =
      RingHom.comp e.toRingHom
        (algebraMap k (GlobalPlace.rationalInfinity k).residueField) := by
    ext c
    change GlobalPlace.constantsToResidue (xAdicPlace k) c =
      e (GlobalPlace.constantsToResidue (GlobalPlace.rationalInfinity k) c)
    exact (rationalInfinityResidueEquivXAdic_constants (k := k) c).symm
  exact (Algebra.trace_eq_of_equiv_equiv (RingEquiv.refl k) e he z).symm
end QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
open scoped Polynomial RatFunc WithZero
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
theorem _root_.solution
    (omega : Differential k (RatFunc k))
    (homega : omega ∈ Differential.simplePoleDifferentialLattice
      (GlobalPlace.rationalInfinity k)) :
    ∃ htransport : rationalDifferentialInvolution (k := k) omega ∈
        Differential.simplePoleDifferentialLattice (xAdicPlace k),
      Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
          (xAdicPlace k) (rationalDifferentialInvolution (k := k) omega)
          htransport =
        Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalInfinity k) omega homega := by
  let P := GlobalPlace.rationalInfinity k
  let Q := xAdicPlace k
  let e := InverseAffinePlace.rationalInvolution k
  let eO := rationalInfinityValuationRingEquivXAdic (k := k)
  let eκ := rationalInfinityResidueEquivXAdic (k := k)
  let pi : P.valuationRing := P.uniformizerInValuationRing
  let r : P.valuationRing :=
    Differential.simplePoleResidueCoordinate (k := k) (F := RatFunc k) P
      ⟨omega, homega⟩
  have hpi : (pi : RatFunc k) ≠ 0 := by
    change P.uniformizer ≠ 0
    exact Differential.localParameter_ne_zero (k := k) (F := RatFunc k) P
  have hepi : e (pi : RatFunc k) ≠ 0 :=
    (map_ne_zero_iff _ e.injective).mpr hpi
  have homegaDecomposition :
      omega = (r : RatFunc k) •
        Differential.logarithmicDifferential (k := k) (F := RatFunc k)
          (pi : RatFunc k) := by
    exact
      Differential.simplePoleDifferential_eq_residueCoordinate_smul_uniformizerLogDifferential
        (k := k) (F := RatFunc k) P ⟨omega, homega⟩
  have htransportDecomposition :
      rationalDifferentialInvolution (k := k) omega =
        ((eO r : Q.valuationRing) : RatFunc k) •
          Differential.logarithmicDifferential (k := k) (F := RatFunc k)
            (e (pi : RatFunc k)) := by
    calc
      rationalDifferentialInvolution (k := k) omega =
          rationalDifferentialInvolution (k := k)
            ((r : RatFunc k) •
              Differential.logarithmicDifferential (k := k) (F := RatFunc k)
                (pi : RatFunc k)) := by rw [homegaDecomposition]
      _ = e (r : RatFunc k) •
          rationalDifferentialInvolution (k := k)
            (Differential.logarithmicDifferential
              (k := k) (F := RatFunc k) (pi : RatFunc k)) := by
        rw [rationalDifferentialInvolution_smul]
      _ = ((eO r : Q.valuationRing) : RatFunc k) •
          Differential.logarithmicDifferential (k := k) (F := RatFunc k)
            (e (pi : RatFunc k)) := by
        rw [rationalDifferentialInvolution_logarithmicDifferential]
        rfl
  let logAt : Differential.simplePoleDifferentialLattice Q :=
    Differential.logarithmicDifferentialAtSimplePole
      (k := k) (F := RatFunc k) Q (e (pi : RatFunc k)) hepi
  have htransport : rationalDifferentialInvolution (k := k) omega ∈
      Differential.simplePoleDifferentialLattice Q := by
    rw [htransportDecomposition]
    exact (Differential.simplePoleDifferentialLattice Q).smul_mem
      (eO r) logAt.property
  refine ⟨htransport, ?_⟩
  have htransportSubtype :
      (⟨rationalDifferentialInvolution (k := k) omega, htransport⟩ :
          Differential.simplePoleDifferentialLattice Q) = eO r • logAt := by
    apply Subtype.ext
    exact htransportDecomposition
  have horder : Q.order (e (pi : RatFunc k)) = 1 := by
    change (xAdicPlace k).order
        (InverseAffinePlace.rationalInvolution k (pi : RatFunc k)) = 1
    rw [xAdic_order_rationalInvolution_eq_rationalInfinity_order]
    exact P.order_uniformizer
  have hresidue :
      Differential.simplePoleResidue (k := k) (F := RatFunc k) Q
          ⟨rationalDifferentialInvolution (k := k) omega, htransport⟩ =
        eκ (Differential.simplePoleResidue (k := k) (F := RatFunc k) P
          ⟨omega, homega⟩) := by
    rw [htransportSubtype,
      Differential.simplePoleResidue_smul,
      show logAt = Differential.logarithmicDifferentialAtSimplePole
        (k := k) (F := RatFunc k) Q (e (pi : RatFunc k)) hepi from rfl,
      Differential.simplePoleResidue_logarithmicDifferential,
      horder, Int.cast_one, mul_one,
      Differential.simplePoleResidue_eq_residueCoordinate]
    exact (rationalInfinityResidueEquivXAdic_residue (k := k) r).symm
  letI : Algebra k P.residueField := GlobalPlace.residueAlgebra P
  letI : FiniteDimensional k P.residueField :=
    GlobalPlace.residueField_finiteDimensional P
  letI : Algebra k Q.residueField := GlobalPlace.residueAlgebra Q
  letI : FiniteDimensional k Q.residueField :=
    GlobalPlace.residueField_finiteDimensional Q
  change Algebra.trace k Q.residueField
      (Differential.simplePoleResidue (k := k) (F := RatFunc k) Q
        ⟨rationalDifferentialInvolution (k := k) omega, htransport⟩) =
    Algebra.trace k P.residueField
      (Differential.simplePoleResidue (k := k) (F := RatFunc k) P
        ⟨omega, homega⟩)
  rw [hresidue]
  exact trace_rationalInfinityResidueEquivXAdic
    (k := k) (Differential.simplePoleResidue (k := k) (F := RatFunc k) P
      ⟨omega, homega⟩)
end QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
