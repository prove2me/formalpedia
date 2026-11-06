-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_mem_directChartFractionalLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:29:36.999889+00:00
-- url     : https://prove2.me/submissions/2468d052-c4b6-44c1-be9f-1eafb36da657

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_AffineCountBridge
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_ChartContainment
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_directChartDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_mem_chartFractionalLattice_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_riemannRochSubmodule_iff


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
variable [τ : IsScalarTower k[X] k⟮X⟯ F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable k⟮X⟯ F]
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
theorem _root_.solution :
    letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
    ∀ (G : Divisor (GlobalPlace k F)) (x : GlobalPlace.riemannRochSubmodule G),
      (x : F) ∈ AffinePlace.chartFractionalLattice k F
        (GlobalPlace.directChartDivisor k F G) := by
  letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  intro G x
  rw [AffinePlace.mem_chartFractionalLattice_iff]
  intro P
  have hx := (GlobalPlace.mem_riemannRochSubmodule_iff G (x : F)).mp x.property
  calc
    AffinePlace.valuation k F P (x : F) =
        (AffinePlace.globalPlace k F P).valuation (x : F) := rfl
    _ ≤ WithZero.exp (G (AffinePlace.globalPlace k F P)) :=
      hx (AffinePlace.globalPlace k F P)
    _ = WithZero.exp (GlobalPlace.directChartDivisor k F G P) := by
      rw [GlobalPlace.directChartDivisor_apply]
end GlobalPlace
end QEC.Coding.AlgebraicGeometry
