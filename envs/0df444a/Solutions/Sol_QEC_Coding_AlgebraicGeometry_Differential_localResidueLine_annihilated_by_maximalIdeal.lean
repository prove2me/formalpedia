-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.localResidueLine_annihilated_by_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:28:37.540973+00:00
-- url     : https://prove2.me/submissions/e6ffba17-1509-4024-9df1-956819c2689b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_maximalIdeal_eq_span_uniformizer

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
open QEC.Coding.AlgebraicGeometry.Differential
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution (P : GlobalPlace k F) :
    Module.IsTorsionBySet P.valuationRing (localResidueLine P)
      (IsLocalRing.maximalIdeal P.valuationRing) := by
  change Module.IsTorsionBySet P.valuationRing
    (simplePoleDifferentialLattice P ⧸ regularDifferentialSubmoduleOfSimplePole P)
    (IsLocalRing.maximalIdeal P.valuationRing)
  rw [Module.isTorsionBySet_quotient_iff]
  intro x r hr
  let I : Ideal P.valuationRing :=
    (localDifferentialLattice P).comap
      (LinearMap.toSpanSingleton P.valuationRing (Differential k F)
        (x : Differential k F))
  have hspan :
      Ideal.span ({P.uniformizerInValuationRing} : Set P.valuationRing) ≤ I := by
    refine Ideal.span_le.2 ?_
    intro y hy
    have hy' : y = P.uniformizerInValuationRing := Set.mem_singleton_iff.mp hy
    subst y
    change P.uniformizerInValuationRing • (x : Differential k F) ∈
      localDifferentialLattice P
    exact x.property
  rw [P.maximalIdeal_eq_span_uniformizer] at hr
  have hrI : r ∈ I := hspan hr
  change r • (x : Differential k F) ∈ localDifferentialLattice P
  change r • (x : Differential k F) ∈ localDifferentialLattice P at hrI
  exact hrI
end QEC.Coding.AlgebraicGeometry.Differential
