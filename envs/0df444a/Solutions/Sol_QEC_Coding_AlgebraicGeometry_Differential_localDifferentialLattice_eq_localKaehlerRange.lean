-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.localDifferentialLattice_eq_localKaehlerRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:28:01.020106+00:00
-- url     : https://prove2.me/submissions/232803e6-8cb5-49e3-9552-69aa4853debd

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing


section
namespace QEC.Coding.AlgebraicGeometry
open scoped WithZero
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
namespace Differential
private theorem derivation_span_eq_liftKaehler_range
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (D : Derivation R S M) :
    Submodule.span S (Set.range D) = D.liftKaehlerDifferential.range := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨KaehlerDifferential.D R S x, D.liftKaehlerDifferential_comp_D x⟩
  · rintro y ⟨omega, rfl⟩
    have homega : omega ∈ Submodule.span S
        (Set.range (KaehlerDifferential.D R S)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ homega
    · rintro _ ⟨x, rfl⟩
      rw [D.liftKaehlerDifferential_comp_D]
      exact Submodule.subset_span (show D x ∈ Set.range D from ⟨x, rfl⟩)
    · exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    · intro a x _ hx
      rw [map_smul]
      exact Submodule.smul_mem _ a hx
end Differential
namespace GlobalPlace
end GlobalPlace
namespace Differential
end Differential
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
open QEC.Coding.AlgebraicGeometry.Differential
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (P : GlobalPlace k F) :
    letI : Algebra k P.valuationRing :=
      (GlobalPlace.constantsToValuationRing P).toAlgebra
    letI : IsScalarTower k P.valuationRing F :=
      IsScalarTower.of_algebraMap_eq fun c => by
        change algebraMap k F c =
          ((GlobalPlace.constantsToValuationRing P c : P.valuationRing) : F)
        exact (GlobalPlace.coe_constantsToValuationRing P c).symm
    localDifferentialLattice P =
      (Derivation.liftKaehlerDifferential
        (Derivation.compAlgebraMap (A := P.valuationRing)
          (KaehlerDifferential.D k F))).range := by
  letI : Algebra k P.valuationRing :=
    (GlobalPlace.constantsToValuationRing P).toAlgebra
  letI : IsScalarTower k P.valuationRing F :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change algebraMap k F c =
        ((GlobalPlace.constantsToValuationRing P c : P.valuationRing) : F)
      exact (GlobalPlace.coe_constantsToValuationRing P c).symm
  let D : Derivation k P.valuationRing (Differential k F) :=
    (KaehlerDifferential.D k F).compAlgebraMap P.valuationRing
  change Submodule.span P.valuationRing (Set.range D) =
    D.liftKaehlerDifferential.range
  exact derivation_span_eq_liftKaehler_range D
end QEC.Coding.AlgebraicGeometry.Differential
