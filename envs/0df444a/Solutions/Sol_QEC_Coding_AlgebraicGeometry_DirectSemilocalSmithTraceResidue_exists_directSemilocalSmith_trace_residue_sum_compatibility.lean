-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue.exists_directSemilocalSmith_trace_residue_sum_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:56:28.150197+00:00
-- url     : https://prove2.me/submissions/8612b846-86a4-4d94-890e-1bdb53247866

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSmithTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalCokernelTraceSum
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SmithDifferentialTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalSmithTraceResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSemilocalSmithTraceResidue_simplePoleResidue_rationalAdicSmith_eq_sum_factorResidueTraces
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicSmithLogarithmicDifferential_eq_functionFieldDifferentialTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSemilocalPrincipalFactorization_exists_directSemilocalUniformizerFactorization
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_exists_smith_bases_toMatrix_eq_diagonal_of_commute

section
namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
open DirectFactorSmithTraceResidue
private theorem lmul_comp_lmul (t b : B k F) :
    (Algebra.lmul (R k) (B k F) t).comp
        (Algebra.lmul (R k) (B k F) b) =
      (Algebra.lmul (R k) (B k F) b).comp
        (Algebra.lmul (R k) (B k F) t) := by
  apply LinearMap.ext
  intro x
  change t * (b * x) = b * (t * x)
  ring
end QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue._p2m_local_instance_7f43513034_38
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue._p2m_local_instance_7f43513034_40
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue._p2m_local_instance_7f43513034_50
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue._p2m_local_instance_7f43513034_54
open DirectFactorSmithTraceResidue
namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (b : B k F) :
    ∃ t : B k F, ∃ ht : t ≠ 0,
      ∃ source target : Module.Basis
        (Fin (Module.finrank (R k) (B k F))) (R k) (B k F),
      ∃ a : Fin (Module.finrank (R k) (B k F)) → R k,
      ∃ ha : ∀ i, a i ≠ 0,
        LinearMap.toMatrix source target
            (Algebra.lmul (R k) (B k F) t) = Matrix.diagonal a ∧
        (∀ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          GlobalPlace.order
              (AffinePlace.globalPlace k F
                (DirectIntegralDifferentialResidue.directFactorPlace k F p P))
              (algebraMap (B k F) F t) = 1) ∧
        ((Differential.rationalAdicSmithLogarithmicDifferentialAtSimplePole p
            source target a ha (Algebra.lmul (R k) (B k F) b) :
              Differential.simplePoleDifferentialLattice
                (GlobalPlace.rationalAdic p)) :
            Differential k (RatFunc k)) =
          FunctionFieldDifferential.functionFieldDifferentialTrace
            (k := k) (F := F)
            ((algebraMap (B k F) F b) •
              Differential.logarithmicDifferential (k := k) (F := F)
                (algebraMap (B k F) F t)) ∧
        Differential.simplePoleResidue (k := k) (F := RatFunc k)
            (GlobalPlace.rationalAdic p)
            (Differential.rationalAdicSmithLogarithmicDifferentialAtSimplePole
              p source target a ha (Algebra.lmul (R k) (B k F) b)) =
          directBaseResidueRationalAdicEquiv k p
            (∑ P : (factors
                (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
              Ideal.Factors.factorResidueTrace p.asIdeal P b) := by
  obtain ⟨t, ht, J, hspan, hcop, horder⟩ :=
    DirectSemilocalPrincipalFactorization.exists_directSemilocalUniformizerFactorization
      k F p
  let basis : Module.Basis
      (Fin (Module.finrank (R k) (B k F))) (R k) (B k F) :=
    Module.finBasis (R k) (B k F)
  have hf : Function.Injective (Algebra.lmul (R k) (B k F) t) := by
    intro x y hxy
    change t * x = t * y at hxy
    exact mul_left_cancel₀ ht hxy
  have hcomm := lmul_comp_lmul k F t b
  obtain ⟨source, target, a, ha, hdiag, _hgdiag⟩ :=
    exists_smith_bases_toMatrix_eq_diagonal_of_commute basis
      (Algebra.lmul (R k) (B k F) t)
      (Algebra.lmul (R k) (B k F) b) hf hcomm
  refine ⟨t, ht, source, target, a, ha, hdiag, horder, ?_, ?_⟩
  · exact
      Differential.coe_rationalAdicSmithLogarithmicDifferential_eq_functionFieldDifferentialTrace
        (k := k) (F := F) p source target a ha t b ht hdiag
  · exact simplePoleResidue_rationalAdicSmith_eq_sum_factorResidueTraces
      k F p J hcop t b hspan source target a ha hdiag
end QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue
