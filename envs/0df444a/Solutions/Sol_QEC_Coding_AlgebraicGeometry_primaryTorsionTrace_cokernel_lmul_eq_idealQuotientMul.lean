-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_cokernel_lmul_eq_idealQuotientMul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:29:36.633715+00:00
-- url     : https://prove2.me/submissions/358e7d68-2f51-46f5-b694-2fc8bc52d4b0

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_SmithTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrincipalCokernelTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_cokernel_lmul_eq_idealQuotientMul_of_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v
variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
attribute [local instance] QEC.Coding.AlgebraicGeometry.principalCokernelModuleFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.idealQuotientModuleFinite
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [IsNoetherianRing R] [Module.Finite R S]
    (p : Ideal R) [p.IsMaximal] (t b : S) (depth : ℕ) :
    primaryTorsionTrace p
        (principalCokernelMul (R := R) t b) depth =
      primaryTorsionTrace p
        (Algebra.lmul R (S ⧸ Ideal.span ({t} : Set S))
          (Ideal.Quotient.mk (Ideal.span ({t} : Set S)) b)) depth := by
  exact primaryTorsionTrace_cokernel_lmul_eq_idealQuotientMul_of_eq
    p t b (Ideal.span ({t} : Set S)) rfl depth
end QEC.Coding.AlgebraicGeometry
