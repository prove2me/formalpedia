-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_quotientMul_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:21:38.089058+00:00
-- url     : https://prove2.me/submissions/280c163e-79d7-4276-80df-80dae1ccb6df

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_ProdTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceEquivScoped
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CRTTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_eq_of_intertwining
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_prodMap_eq_add

section
namespace QEC.Coding.AlgebraicGeometry
universe u v
variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
@[simp]
private theorem quotientMulLinearEquivQuotientProd_apply
    (I J : Ideal S) (hcop : IsCoprime I J) (x : S ⧸ (I * J)) :
    quotientMulLinearEquivQuotientProd (R := R) I J hcop x =
      Ideal.quotientMulEquivQuotientProd I J hcop x :=
  rfl
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v
variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [IsNoetherianRing R] [Module.Finite R S]
    (p : Ideal R) [p.IsMaximal]
    (I J : Ideal S) (hcop : IsCoprime I J)
    (b : S) (depth : ℕ) :
    primaryTorsionTrace p
        (Algebra.lmul R (S ⧸ (I * J)) (Ideal.Quotient.mk (I * J) b)) depth =
      primaryTorsionTrace p
          (Algebra.lmul R (S ⧸ I) (Ideal.Quotient.mk I b)) depth +
        primaryTorsionTrace p
          (Algebra.lmul R (S ⧸ J) (Ideal.Quotient.mk J b)) depth := by
  let eRing := Ideal.quotientMulEquivQuotientProd I J hcop
  let e := quotientMulLinearEquivQuotientProd (R := R) I J hcop
  let fIJ := Algebra.lmul R (S ⧸ (I * J)) (Ideal.Quotient.mk (I * J) b)
  let fI := Algebra.lmul R (S ⧸ I) (Ideal.Quotient.mk I b)
  let fJ := Algebra.lmul R (S ⧸ J) (Ideal.Quotient.mk J b)
  have hintertwines : (e : (S ⧸ (I * J)) →ₗ[R] (S ⧸ I) × (S ⧸ J)).comp fIJ =
      (fI.prodMap fJ).comp
        (e : (S ⧸ (I * J)) →ₗ[R] (S ⧸ I) × (S ⧸ J)) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, fIJ, fI, fJ,
      LinearMap.prodMap_apply, e]
    change eRing (Ideal.Quotient.mk (I * J) b * x) =
      (Ideal.Quotient.mk I b * (eRing x).1,
        Ideal.Quotient.mk J b * (eRing x).2)
    rw [map_mul]
    apply Prod.ext <;>
      simp [eRing, Ideal.quotientMulEquivQuotientProd_fst,
        Ideal.quotientMulEquivQuotientProd_snd]
  calc
    primaryTorsionTrace p fIJ depth =
        primaryTorsionTrace p (fI.prodMap fJ) depth :=
      primaryTorsionTrace_eq_of_intertwining p e fIJ
        (fI.prodMap fJ) hintertwines depth
    _ = _ := primaryTorsionTrace_prodMap_eq_add p fI fJ depth
end QEC.Coding.AlgebraicGeometry
