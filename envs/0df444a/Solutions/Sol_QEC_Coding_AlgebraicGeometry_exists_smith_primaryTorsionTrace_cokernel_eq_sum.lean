-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.exists_smith_primaryTorsionTrace_cokernel_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:29:24.840325+00:00
-- url     : https://prove2.me/submissions/348efc06-8331-48f2-964f-3251627b9300

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialSmithMatrix
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PiTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicTraceStabilization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceEquivScoped
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_SmithTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_cokernel_eq_sum_diagonal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_exists_smith_bases_toMatrix_eq_diagonal_of_commute


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
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [IsNoetherianRing R] [Module.Finite R M]
    {n : ℕ} (b : Basis (Fin n) R M)
    (f g : M →ₗ[R] M) (hf : Function.Injective f)
    (hcomm : f.comp g = g.comp f)
    (q : R) (hq : Irreducible q) [hmax : (Ideal.span {q}).IsMaximal] :
    ∃ source target : Basis (Fin n) R M, ∃ a : Fin n → R,
      (∀ i, a i ≠ 0) ∧
        LinearMap.toMatrix source target f = Matrix.diagonal a ∧
        (∀ i, LinearMap.toMatrix source source g i i =
          LinearMap.toMatrix target target g i i) ∧
        primaryTorsionTrace (Ideal.span {q})
            (cokernelEndomorphism f g hcomm)
              (∑ i, multiplicity q (a i)) =
          ∑ i, (multiplicity q (a i) : R ⧸ Ideal.span {q}) *
            Ideal.Quotient.mk (Ideal.span {q})
              (LinearMap.toMatrix target target g i i) := by
  obtain ⟨source, target, a, ha, hdiag, hgdiag⟩ :=
    exists_smith_bases_toMatrix_eq_diagonal_of_commute b f g hf hcomm
  refine ⟨source, target, a, ha, hdiag, hgdiag, ?_⟩
  apply primaryTorsionTrace_cokernel_eq_sum_diagonal
    source target a ha f g hdiag hcomm q hq
  intro i
  exact Finset.single_le_sum
    (fun j _hj => Nat.zero_le (multiplicity q (a j)))
    (Finset.mem_univ i)
end QEC.Coding.AlgebraicGeometry
