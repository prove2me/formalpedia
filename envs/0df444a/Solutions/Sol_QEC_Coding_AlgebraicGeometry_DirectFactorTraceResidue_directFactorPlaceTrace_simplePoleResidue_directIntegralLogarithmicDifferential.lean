-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue.directFactorPlaceTrace_simplePoleResidue_directIntegralLogarithmicDifferential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:45:20.127467+00:00
-- url     : https://prove2.me/submissions/2a650495-c245-4a56-92cd-2b76d9a18a6f

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorResidueTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorTraceResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorTraceResidue_directFactorPlaceTrace_residue_integral
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectIntegralDifferentialResidue_simplePoleResidue_directIntegralLogarithmicDifferential

section
namespace QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] directFactorTraceResidue_constantAlgebra
open DirectIntegralDifferentialResidue DirectFactorResidueTransport
private theorem directFactorPlaceTrace_mul_baseResidue
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (x : (AffinePlace.globalPlace k F
      (directFactorPlace k F p P)).residueField)
    (r : p.asIdeal.ResidueField) :
    directFactorPlaceTrace k F p P
        (x * directFactorBaseResidueMap k F p P r) =
      r * directFactorPlaceTrace k F p P x := by
  letI : Algebra p.asIdeal.ResidueField
      (AffinePlace.globalPlace k F
        (directFactorPlace k F p P)).residueField :=
    (directFactorBaseResidueMap k F p P).toAlgebra
  change Algebra.trace p.asIdeal.ResidueField
      (AffinePlace.globalPlace k F
        (directFactorPlace k F p P)).residueField
        (x * algebraMap p.asIdeal.ResidueField
          (AffinePlace.globalPlace k F
            (directFactorPlace k F p P)).residueField r) =
    r * Algebra.trace p.asIdeal.ResidueField
      (AffinePlace.globalPlace k F
        (directFactorPlace k F p P)).residueField x
  rw [mul_comm]
  exact map_smul (Algebra.trace p.asIdeal.ResidueField
      (AffinePlace.globalPlace k F
        (directFactorPlace k F p P)).residueField) r x
end QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue
end

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
        (Differential.simplePoleResidue (k := k) (F := F)
          (AffinePlace.globalPlace k F (directFactorPlace k F p P))
          (directIntegralLogarithmicDifferentialAtSimplePole k F p P b)) =
      (p.asIdeal.ramificationIdx' (P : Ideal (B k F)) :
          p.asIdeal.ResidueField) *
        Ideal.Factors.factorResidueTrace p.asIdeal P b := by
  rw [simplePoleResidue_directIntegralLogarithmicDifferential]
  have hcast :
      (p.asIdeal.ramificationIdx' (P : Ideal (B k F)) :
          (AffinePlace.globalPlace k F
            (directFactorPlace k F p P)).residueField) =
        directFactorBaseResidueMap k F p P
          (p.asIdeal.ramificationIdx' (P : Ideal (B k F)) :
            p.asIdeal.ResidueField) := by
    symm
    exact map_natCast (directFactorBaseResidueMap k F p P)
      (p.asIdeal.ramificationIdx' (P : Ideal (B k F)))
  rw [hcast, directFactorPlaceTrace_mul_baseResidue,
    directFactorPlaceTrace_residue_integral]
end QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue
