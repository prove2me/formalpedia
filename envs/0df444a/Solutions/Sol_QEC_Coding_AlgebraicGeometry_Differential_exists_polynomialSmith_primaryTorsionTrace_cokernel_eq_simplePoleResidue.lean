-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.exists_polynomialSmith_primaryTorsionTrace_cokernel_eq_simplePoleResidue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:29:26.580943+00:00
-- url     : https://prove2.me/submissions/056230b4-200b-4d52-8e9f-5e2cbacd1e86

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_SmithTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicDiagonalMatrixResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithTraceResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_rationalAdicIdealResidueEquiv_primaryTorsionTrace_cokernel_eq_simplePoleResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_exists_smith_bases_toMatrix_eq_diagonal_of_commute


set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    {N : Type*} [AddCommGroup N] [Module k[X] N] [Module.Finite k[X] N]
    {n : ℕ} (b : Module.Basis (Fin n) k[X] N)
    (f g : N →ₗ[k[X]] N) (hf : Function.Injective f)
    (hcomm : f.comp g = g.comp f)
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    ∃ source target : Module.Basis (Fin n) k[X] N, ∃ a : Fin n → k[X],
      ∃ ha : ∀ i, a i ≠ 0,
        LinearMap.toMatrix source target f = Matrix.diagonal a ∧
        (∀ i, LinearMap.toMatrix source source g i i =
          LinearMap.toMatrix target target g i i) ∧
        GlobalPlace.rationalAdicIdealResidueEquiv p
            (primaryTorsionTrace p.asIdeal
              (cokernelEndomorphism f g hcomm)
                (∑ i, multiplicity p.asIdeal
                  (Ideal.span ({a i} : Set k[X])))) =
          simplePoleResidue (k := k) (F := RatFunc k)
            (GlobalPlace.rationalAdic p)
            (rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
              (LinearMap.toMatrix target target g) a ha) := by
  obtain ⟨source, target, a, ha, hdiag, hgdiag⟩ :=
    exists_smith_bases_toMatrix_eq_diagonal_of_commute b f g hf hcomm
  refine ⟨source, target, a, ha, hdiag, hgdiag, ?_⟩
  apply
    rationalAdicIdealResidueEquiv_primaryTorsionTrace_cokernel_eq_simplePoleResidue
      source target a ha f g hdiag hcomm p
  intro i
  exact Finset.single_le_sum
    (fun j _hj => Nat.zero_le
      (multiplicity p.asIdeal (Ideal.span ({a j} : Set k[X]))))
    (Finset.mem_univ i)
end QEC.Coding.AlgebraicGeometry.Differential
