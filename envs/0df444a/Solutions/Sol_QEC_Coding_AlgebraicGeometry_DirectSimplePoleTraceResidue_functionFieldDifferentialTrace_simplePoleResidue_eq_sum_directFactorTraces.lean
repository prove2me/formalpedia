-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectSimplePoleTraceResidue.functionFieldDifferentialTrace_simplePoleResidue_eq_sum_directFactorTraces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:59:46.676371+00:00
-- url     : https://prove2.me/submissions/2e09c292-faac-4f4c-b2a2-3b9b35d8edf3

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorResidueTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalDifferentialTraceRegularity
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalSmithTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SimplePoleTraceResidue
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_localDifferentialLattice_le_simplePoleDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_logarithmicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorTraceResidue_directFactorPlaceTrace_residue_integral
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSemilocalDifferentialTraceRegularity_functionFieldDifferentialTrace_mem_rationalAdic_of_mem_directFactorLattices
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSemilocalSmithTraceResidue_exists_directSemilocalSmith_trace_residue_sum_compatibility
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
attribute [local simp] Ideal.Factors.quotientResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv_quotientResidueEquiv
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicIdealResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply


section
namespace QEC.Coding.AlgebraicGeometry.DirectSimplePoleTraceResidue
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] simplePoleTraceResidue_Algebra_1
attribute [local instance] simplePoleTraceResidue_ScalarTower_1
open DirectFactorResidueTransport DirectFactorTraceResidue
open DirectIntegralDifferentialResidue
open DirectSemilocalDifferentialTraceRegularity
open DirectSemilocalSmithTraceResidue
open FunctionFieldDifferential
omit [Finite k] in
private theorem directFactors_isCoprime_of_ne
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P Q : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (hPQ : P ≠ Q) :
    IsCoprime (P : Ideal (B k F)) (Q : Ideal (B k F)) := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply Ideal.IsMaximal.coprime_of_ne
    ((Ideal.Factors.isPrime p.asIdeal P).isMaximal
      (Ideal.Factors.ne_bot p.asIdeal P))
    ((Ideal.Factors.isPrime p.asIdeal Q).isMaximal
      (Ideal.Factors.ne_bot p.asIdeal Q))
  intro hideal
  apply hPQ
  exact Subtype.ext hideal
private theorem exists_directIntegral_with_factorResidues
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (rho : ∀ P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      (AffinePlace.globalPlace k F
        (directFactorPlace k F p P)).residueField) :
    ∃ b : B k F,
      ∀ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
        (AffinePlace.globalPlace k F
          (directFactorPlace k F p P)).residue
            (directIntegralToValuationRing k F p P b) = rho P := by
  classical
  let I := fun P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset =>
    (P : Ideal (B k F))
  have hI : Pairwise fun P Q => IsCoprime (I P) (I Q) := by
    intro P Q hPQ
    exact directFactors_isCoprime_of_ne k F p P Q hPQ
  let x : ∀ P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      B k F ⧸ I P := fun P => by
    letI : (P : Ideal (B k F)).IsMaximal :=
      (Ideal.Factors.isPrime p.asIdeal P).isMaximal
        (Ideal.Factors.ne_bot p.asIdeal P)
    exact (Ideal.Factors.quotientResidueEquiv (P : Ideal (B k F))).symm
      ((directFactorResidueEquiv k F p P).symm (rho P))
  obtain ⟨b, hb⟩ := Ideal.pi_quotient_surjective hI x
  refine ⟨b, ?_⟩
  intro P
  letI : (P : Ideal (B k F)).IsMaximal :=
    (Ideal.Factors.isPrime p.asIdeal P).isMaximal
      (Ideal.Factors.ne_bot p.asIdeal P)
  rw [← directFactorResidueEquiv_algebraMap]
  change directFactorResidueEquiv k F p P
      (Ideal.Factors.quotientResidueEquiv (P : Ideal (B k F))
        (Ideal.Quotient.mk (P : Ideal (B k F)) b)) = rho P
  rw [hb P]
  simp only [x, RingEquiv.apply_symm_apply]
private theorem mem_localDifferentialLattice_of_simplePoleResidue_eq_zero
    (P : GlobalPlace k F)
    (omega : Differential.simplePoleDifferentialLattice P)
    (homega : Differential.simplePoleResidue (k := k) (F := F) P omega = 0) :
    (omega : Differential k F) ∈ Differential.localDifferentialLattice P := by
  change omega ∈ Differential.regularDifferentialSubmoduleOfSimplePole P
  apply (Submodule.Quotient.mk_eq_zero
    (p := Differential.regularDifferentialSubmoduleOfSimplePole P)
    (x := omega)).mp
  apply (Differential.simplePoleResidueEquiv (k := k) (F := F) P).injective
  simp only [map_zero]
  exact homega
end QEC.Coding.AlgebraicGeometry.DirectSimplePoleTraceResidue
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectSimplePoleTraceResidue
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSimplePoleTraceResidue.simplePoleTraceResidue_Algebra_1
attribute [local instance] simplePoleTraceResidue_Algebra_1
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSimplePoleTraceResidue.simplePoleTraceResidue_ScalarTower_1
attribute [local instance] simplePoleTraceResidue_ScalarTower_1
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSimplePoleTraceResidue._p2m_local_instance_fead31de17_60
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSimplePoleTraceResidue._p2m_local_instance_fead31de17_64
open DirectFactorResidueTransport DirectFactorTraceResidue
open DirectIntegralDifferentialResidue
open DirectSemilocalDifferentialTraceRegularity
open DirectSemilocalSmithTraceResidue
open FunctionFieldDifferential
namespace QEC.Coding.AlgebraicGeometry.DirectSimplePoleTraceResidue
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (omega : Differential k F)
    (homega : ∀ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      omega ∈ Differential.simplePoleDifferentialLattice
        (AffinePlace.globalPlace k F (directFactorPlace k F p P))) :
    ∃ htrace : functionFieldDifferentialTrace (k := k) (F := F) omega ∈
        Differential.simplePoleDifferentialLattice
          (GlobalPlace.rationalAdic p),
      Differential.simplePoleResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p)
          ⟨functionFieldDifferentialTrace (k := k) (F := F) omega, htrace⟩ =
        DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv k p
          (∑ P : (factors
              (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
            directFactorPlaceTrace k F p P
              (Differential.simplePoleResidue (k := k) (F := F)
                (AffinePlace.globalPlace k F (directFactorPlace k F p P))
                ⟨omega, homega P⟩)) := by
  classical
  let rho := fun P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset =>
    Differential.simplePoleResidue (k := k) (F := F)
      (AffinePlace.globalPlace k F (directFactorPlace k F p P))
      ⟨omega, homega P⟩
  obtain ⟨b, hb⟩ := exists_directIntegral_with_factorResidues k F p rho
  obtain ⟨t, ht, source, target, a, ha, hdiag, horder,
      htraceModel, hresidueModel⟩ :=
    exists_directSemilocalSmith_trace_residue_sum_compatibility k F p b
  let model : Differential k F :=
    algebraMap (B k F) F b •
      Differential.logarithmicDifferential (k := k) (F := F)
        (algebraMap (B k F) F t)
  let eta : Differential k F := omega - model
  let modelAt := fun P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset =>
    DirectFactorSemilocalLogarithmicResidue.directFactorSemilocalLogarithmicDifferentialAtSimplePole
      k F p P t ht b
  have hmodelResidue : ∀ P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      Differential.simplePoleResidue (k := k) (F := F)
          (AffinePlace.globalPlace k F (directFactorPlace k F p P))
          (modelAt P) = rho P := by
    intro P
    unfold modelAt
    unfold DirectFactorSemilocalLogarithmicResidue.directFactorSemilocalLogarithmicDifferentialAtSimplePole
    rw [Differential.simplePoleResidue_smul,
      Differential.simplePoleResidue_logarithmicDifferential,
      horder P, Int.cast_one, mul_one]
    exact hb P
  have hetaSimple : ∀ P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      eta ∈ Differential.simplePoleDifferentialLattice
        (AffinePlace.globalPlace k F (directFactorPlace k F p P)) := by
    intro P
    have hsub := (Differential.simplePoleDifferentialLattice
      (AffinePlace.globalPlace k F (directFactorPlace k F p P))).sub_mem
        (homega P) (modelAt P).property
    exact hsub
  have hetaResidueZero : ∀ P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      Differential.simplePoleResidue (k := k) (F := F)
          (AffinePlace.globalPlace k F (directFactorPlace k F p P))
          ⟨eta, hetaSimple P⟩ = 0 := by
    intro P
    have hsubtype :
        (⟨eta, hetaSimple P⟩ : Differential.simplePoleDifferentialLattice
          (AffinePlace.globalPlace k F (directFactorPlace k F p P))) =
          ⟨omega, homega P⟩ - modelAt P := by
      apply Subtype.ext
      rfl
    rw [hsubtype, map_sub, hmodelResidue P]
    change rho P - rho P = 0
    exact sub_self _
  have hetaRegular : ∀ P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      eta ∈ Differential.localDifferentialLattice
        (AffinePlace.globalPlace k F (directFactorPlace k F p P)) := by
    intro P
    exact mem_localDifferentialLattice_of_simplePoleResidue_eq_zero
      k F _ ⟨eta, hetaSimple P⟩ (hetaResidueZero P)
  have htraceEtaRegular :
      functionFieldDifferentialTrace (k := k) (F := F) eta ∈
        Differential.localDifferentialLattice (GlobalPlace.rationalAdic p) :=
    functionFieldDifferentialTrace_mem_rationalAdic_of_mem_directFactorLattices
      k F p eta hetaRegular
  let smithAt : Differential.simplePoleDifferentialLattice
      (GlobalPlace.rationalAdic p) :=
    Differential.rationalAdicSmithLogarithmicDifferentialAtSimplePole p
      source target a ha (Algebra.lmul (R k) (B k F) b)
  have htraceModelSimple :
      functionFieldDifferentialTrace (k := k) (F := F) model ∈
        Differential.simplePoleDifferentialLattice
          (GlobalPlace.rationalAdic p) := by
    rw [← htraceModel]
    exact smithAt.property
  have htraceEtaSimple :
      functionFieldDifferentialTrace (k := k) (F := F) eta ∈
        Differential.simplePoleDifferentialLattice
          (GlobalPlace.rationalAdic p) :=
    Differential.localDifferentialLattice_le_simplePoleDifferentialLattice
      (k := k) (F := RatFunc k) (GlobalPlace.rationalAdic p) htraceEtaRegular
  have homegaDecomposition : omega = eta + model := by
    dsimp only [eta]
    abel
  have htraceDecomposition :
      functionFieldDifferentialTrace (k := k) (F := F) omega =
        functionFieldDifferentialTrace (k := k) (F := F) eta +
          functionFieldDifferentialTrace (k := k) (F := F) model := by
    rw [homegaDecomposition, map_add]
  have htraceSimple :
      functionFieldDifferentialTrace (k := k) (F := F) omega ∈
        Differential.simplePoleDifferentialLattice
          (GlobalPlace.rationalAdic p) := by
    rw [htraceDecomposition]
    exact (Differential.simplePoleDifferentialLattice
      (GlobalPlace.rationalAdic p)).add_mem htraceEtaSimple htraceModelSimple
  refine ⟨htraceSimple, ?_⟩
  let traceEtaAt : Differential.simplePoleDifferentialLattice
      (GlobalPlace.rationalAdic p) :=
    ⟨functionFieldDifferentialTrace (k := k) (F := F) eta,
      htraceEtaSimple⟩
  have htraceSubtype :
      (⟨functionFieldDifferentialTrace (k := k) (F := F) omega, htraceSimple⟩ :
          Differential.simplePoleDifferentialLattice
            (GlobalPlace.rationalAdic p)) =
        traceEtaAt + smithAt := by
    apply Subtype.ext
    change functionFieldDifferentialTrace (k := k) (F := F) omega =
      functionFieldDifferentialTrace (k := k) (F := F) eta +
        (smithAt : Differential k (RatFunc k))
    rw [htraceDecomposition, htraceModel]
  have hsum :
      (∑ P : (factors
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
        Ideal.Factors.factorResidueTrace p.asIdeal P b) =
        ∑ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          directFactorPlaceTrace k F p P (rho P) := by
    apply Finset.sum_congr rfl
    intro P _
    rw [← hb P]
    exact (directFactorPlaceTrace_residue_integral k F p P b).symm
  calc
    Differential.simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        ⟨functionFieldDifferentialTrace (k := k) (F := F) omega,
          htraceSimple⟩ =
      Differential.simplePoleResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p) traceEtaAt +
        Differential.simplePoleResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p) smithAt := by
      rw [htraceSubtype, map_add]
    _ = Differential.simplePoleResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p) smithAt := by
      rw [Differential.simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
        (k := k) (F := RatFunc k) (GlobalPlace.rationalAdic p)
        traceEtaAt htraceEtaRegular, zero_add]
    _ = DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv k p
        (∑ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          Ideal.Factors.factorResidueTrace p.asIdeal P b) := hresidueModel
    _ = DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv k p
        (∑ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          directFactorPlaceTrace k F p P (rho P)) := by rw [hsum]
    _ = _ := rfl
end QEC.Coding.AlgebraicGeometry.DirectSimplePoleTraceResidue
