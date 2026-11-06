-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.exists_polynomialSmith_primaryTorsionTrace_cokernel_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:29:25.641091+00:00
-- url     : https://prove2.me/submissions/d2187540-4d26-4720-88b8-83c90e24386e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialSmithMatrix
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PiTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicTraceStabilization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceEquivScoped
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_SmithTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_cokernel_eq_sum_diagonal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicPolynomial_irreducible
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_exists_smith_bases_toMatrix_eq_diagonal_of_commute
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_multiplicity_span_singleton_eq

section
open scoped Polynomial
namespace QEC.Coding.AlgebraicGeometry
open Module
universe u v
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [IsDomain R] [IsPrincipalIdealRing R]
variable {k : Type*} [Field k] [Finite k]
private theorem primaryTorsionTrace_cokernel_eq_sum_diagonal_of_eq_span
    {N : Type*} [AddCommGroup N] [Module k[X] N] [Module.Finite k[X] N]
    {n : ℕ} (source target : Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (f g : N →ₗ[k[X]] N)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (hcomm : f.comp g = g.comp f)
    (P : Ideal k[X]) [P.IsMaximal]
    (q : k[X]) (hq : Irreducible q) (hP : P = Ideal.span {q})
    (depth : ℕ)
    (hdepth : ∀ i, multiplicity P (Ideal.span ({a i} : Set k[X])) ≤ depth) :
    primaryTorsionTrace P (cokernelEndomorphism f g hcomm) depth =
      ∑ i, (multiplicity P (Ideal.span ({a i} : Set k[X])) : k[X] ⧸ P) *
        Ideal.Quotient.mk P
          (LinearMap.toMatrix target target g i i) := by
  subst P
  simp_rw [multiplicity_span_singleton_eq q (a _) hq (ha _)] at hdepth ⊢
  exact primaryTorsionTrace_cokernel_eq_sum_diagonal
    source target a ha f g hdiag hcomm q hq depth hdepth
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Module
universe u v
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
attribute [local instance] QEC.Coding.AlgebraicGeometry.cokernelModuleFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.cyclicQuotientModuleFinite
variable [IsDomain R] [IsPrincipalIdealRing R]
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {N : Type*} [AddCommGroup N] [Module k[X] N] [Module.Finite k[X] N]
    {n : ℕ} (b : Basis (Fin n) k[X] N)
    (f g : N →ₗ[k[X]] N) (hf : Function.Injective f)
    (hcomm : f.comp g = g.comp f)
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    ∃ source target : Basis (Fin n) k[X] N, ∃ a : Fin n → k[X],
      (∀ i, a i ≠ 0) ∧
        LinearMap.toMatrix source target f = Matrix.diagonal a ∧
        (∀ i, LinearMap.toMatrix source source g i i =
          LinearMap.toMatrix target target g i i) ∧
        primaryTorsionTrace p.asIdeal
            (cokernelEndomorphism f g hcomm)
              (∑ i, multiplicity p.asIdeal
                (Ideal.span ({a i} : Set k[X]))) =
          ∑ i, (multiplicity p.asIdeal
              (Ideal.span ({a i} : Set k[X])) : k[X] ⧸ p.asIdeal) *
            Ideal.Quotient.mk p.asIdeal
              (LinearMap.toMatrix target target g i i) := by
  obtain ⟨source, target, a, ha, hdiag, hgdiag⟩ :=
    exists_smith_bases_toMatrix_eq_diagonal_of_commute b f g hf hcomm
  refine ⟨source, target, a, ha, hdiag, hgdiag, ?_⟩
  let q := GlobalPlace.rationalAdicPolynomial p
  apply primaryTorsionTrace_cokernel_eq_sum_diagonal_of_eq_span
    source target a ha f g hdiag hcomm p.asIdeal q
      (GlobalPlace.rationalAdicPolynomial_irreducible p)
        (GlobalPlace.rationalAdic_asIdeal_eq_span p)
  intro i
  exact Finset.single_le_sum
    (fun j _hj => Nat.zero_le
      (multiplicity p.asIdeal (Ideal.span ({a j} : Set k[X]))))
    (Finset.mem_univ i)
end QEC.Coding.AlgebraicGeometry
