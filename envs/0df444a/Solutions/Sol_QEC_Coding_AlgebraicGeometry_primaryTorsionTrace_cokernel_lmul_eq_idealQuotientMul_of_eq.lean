-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_cokernel_lmul_eq_idealQuotientMul_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:27:16.202332+00:00
-- url     : https://prove2.me/submissions/3d0a96ea-e713-4e16-a4ca-c9f42e4a56da

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_SmithTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrincipalCokernelTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_eq_of_intertwining

section
namespace QEC.Coding.AlgebraicGeometry
universe u v
variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
private theorem cokernelEndomorphism_mk' (t b x : S) :
    principalCokernelMul (R := R) t b (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (b * x) :=
  rfl
end QEC.Coding.AlgebraicGeometry
end

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
    (p : Ideal R) [p.IsMaximal] (t b : S) (I : Ideal S)
    (hspan : Ideal.span ({t} : Set S) = I) (depth : ℕ) :
    primaryTorsionTrace p
        (principalCokernelMul (R := R) t b) depth =
      primaryTorsionTrace p
        (Algebra.lmul R (S ⧸ I) (Ideal.Quotient.mk I b)) depth := by
  let e := principalCokernelEquivOfEq (R := R) t I hspan
  let f := principalCokernelMul (R := R) t b
  let g := Algebra.lmul R (S ⧸ I) (Ideal.Quotient.mk I b)
  have hintertwines :
      (e : (S ⧸ LinearMap.range (Algebra.lmul R S t)) →ₗ[R]
        S ⧸ I).comp f =
        g.comp (e : (S ⧸ LinearMap.range (Algebra.lmul R S t)) →ₗ[R]
          S ⧸ I) := by
    apply LinearMap.ext
    intro z
    induction z using Quotient.inductionOn' with
    | _ x =>
        change principalCokernelEquivOfEq (R := R) t I hspan
            (principalCokernelMul (R := R) t b
              (Submodule.Quotient.mk x)) =
          Ideal.Quotient.mk I b *
            principalCokernelEquivOfEq (R := R) t I hspan
              (Submodule.Quotient.mk x)
        rw [cokernelEndomorphism_mk', principalCokernelEquivOfEq_mk,
          principalCokernelEquivOfEq_mk, map_mul]
  exact primaryTorsionTrace_eq_of_intertwining p e f g hintertwines depth
end QEC.Coding.AlgebraicGeometry
