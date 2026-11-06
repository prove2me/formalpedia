-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue.directFactorPlaceTrace_residue_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:42:11.660402+00:00
-- url     : https://prove2.me/submissions/a2054cba-471f-41f5-9457-9e5a1b871827

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorResidueTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorTraceResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue.directFactorTraceResidue_constantAlgebra
attribute [local instance] directFactorTraceResidue_constantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue._p2m_local_instance_49470eb06b_39
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue._p2m_local_instance_49470eb06b_49
open DirectIntegralDifferentialResidue DirectFactorResidueTransport
namespace QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    directFactorPlaceTrace k F p P
        ((AffinePlace.globalPlace k F
          (directFactorPlace k F p P)).residue
            (directIntegralToValuationRing k F p P b)) =
      Ideal.Factors.factorResidueTrace p.asIdeal P b := by
  letI : (P : Ideal (B k F)).IsMaximal :=
    (Ideal.Factors.isPrime p.asIdeal P).isMaximal
      (Ideal.Factors.ne_bot p.asIdeal P)
  letI : Algebra (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime (P : Ideal (B k F))) :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal (P : Ideal (B k F))
  let e := directFactorResidueEquiv k F p P
  letI : Algebra p.asIdeal.ResidueField
      (AffinePlace.globalPlace k F
        (directFactorPlace k F p P)).residueField :=
    (directFactorBaseResidueMap k F p P).toAlgebra
  have he : RingHom.comp
      (algebraMap p.asIdeal.ResidueField
        (AffinePlace.globalPlace k F
          (directFactorPlace k F p P)).residueField)
      (RingEquiv.refl p.asIdeal.ResidueField) =
      RingHom.comp (e : (P : Ideal (B k F)).ResidueField →+*
        (AffinePlace.globalPlace k F
          (directFactorPlace k F p P)).residueField)
        (algebraMap p.asIdeal.ResidueField
          (P : Ideal (B k F)).ResidueField) := by
    rfl
  have htrace := Algebra.trace_eq_of_equiv_equiv
    (RingEquiv.refl p.asIdeal.ResidueField) e he
    (algebraMap (B k F) (P : Ideal (B k F)).ResidueField b)
  change Algebra.trace p.asIdeal.ResidueField
      (AffinePlace.globalPlace k F
        (directFactorPlace k F p P)).residueField
        ((AffinePlace.globalPlace k F
          (directFactorPlace k F p P)).residue
            (directIntegralToValuationRing k F p P b)) =
    Algebra.trace p.asIdeal.ResidueField
      (P : Ideal (B k F)).ResidueField
        (algebraMap (B k F) (P : Ideal (B k F)).ResidueField b)
  rw [← directFactorResidueEquiv_algebraMap]
  exact htrace.symm
end QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue
