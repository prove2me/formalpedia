-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.affineDifferentialGlobalSectionsEquiv_D
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:01:55.298176+00:00
-- url     : https://prove2.me/submissions/838d3351-4699-45a2-b2c2-abbc02006b87

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeDifferentials
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialSheafComparison_fac
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialAdditivePresheafMap_top

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
attribute [local instance] QEC.Coding.AlgebraicGeometry.affineDifferentialOmegaOpenAModule
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (a : A) :
    affineDifferentialGlobalSectionsEquiv k A
      ((schemeDifferentialSheafDerivation (Spec A) (CommRingCat.of k) cA).d
        ((Scheme.ΓSpecIso A).inv a)) = KaehlerDifferential.D k A a := by
  have h := PresheafOfModules.Derivation.congr_d
    (affineDifferentialSheafComparison_fac k A) (X := op ⊤) ((Scheme.ΓSpecIso A).inv a)
  have ht := h.trans (affineDifferentialAdditivePresheafMap_top k A a)
  change (tilde.isoTop (R := A) M).toLinearEquiv.symm
    ((affineDifferentialSheafComparison k A).val.app (op ⊤)
      ((schemeDifferentialSheafDerivation (Spec A) (CommRingCat.of k) cA).d
        ((Scheme.ΓSpecIso A).inv a))) = _
  exact (LinearEquiv.symm_apply_eq (tilde.isoTop (R := A) M).toLinearEquiv).mpr ht
end QEC.Coding.AlgebraicGeometry
