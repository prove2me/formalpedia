-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.affineDifferentialSheafComparison_fac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:00:13.59884+00:00
-- url     : https://prove2.me/submissions/7de1d593-d2a0-4eca-a8f7-8d80c03027e4

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeDifferentials
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialSheafDerivation_postcomp


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) (A : CommRingCat.{u}) [CommRing k] [Algebra k A]
local notation "M" => ModuleCat.of A (KaehlerDifferential k A)
local notation "T" => tilde (R := A) M
local notation "B" => @PrimeSpectrum.basicOpen A _
local notation "F" => affineDifferentialUnderlyingRingPresheaf A
local notation "S" => affineDifferentialTildeAbelianSheaf k A
attribute [local instance] basicOpenAlgebra basicOpenLocalization basicOpenModule
  basicOpenAModule basicOpenModuleTower basicOpenBaseAlgebra basicOpenBaseTower
  basicOpenTildeLocalization basicOpenKModule basicOpenKModuleTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.affineDifferentialTildeOpenModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.affineDifferentialTildeBasicModule
local notation "cA" => affineDifferentialGlobalConstantMap k A
local notation "Omegap" => schemeDifferentialPresheaf (Spec A) (CommRingCat.of k) cA
local notation "Omega" => schemeDifferentialSheaf (Spec A) (CommRingCat.of k) cA
local notation "phiA" => schemeConstantPresheafMap (Spec A) (CommRingCat.of k) cA
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution :
    (schemeDifferentialSheafDerivation (Spec A) (CommRingCat.of k) cA).postcomp
      ((Scheme.Modules.toPresheafOfModules (Spec A)).map
        (affineDifferentialSheafComparison k A)) = affineDifferentialTildeDerivation k A := by
  rw [schemeDifferentialSheafDerivation_postcomp]
  exact (schemeDifferentialSheafHomEquiv (Spec A) (CommRingCat.of k) cA T).apply_symm_apply _
end QEC.Coding.AlgebraicGeometry
