-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.affineDifferentialAdditivePresheafMap_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:00:16.14761+00:00
-- url     : https://prove2.me/submissions/f6fd9309-d855-4572-8857-b1e24f4154af

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeDifferentials
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials

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
    (affineDifferentialAdditivePresheafMap k A).app (op ⊤) ((Scheme.ΓSpecIso A).inv a) =
      tilde.toOpen (R := A) M ⊤ (KaehlerDifferential.D k A a) := by
  apply TopCat.Presheaf.IsSheaf.section_ext (S).property
  intro x _hx
  have hx : x ∈ B (1 : A) := by
    let : x.asIdeal.IsPrime := x.isPrime
    exact (PrimeSpectrum.mem_basicOpen (1 : A) x).mpr x.asIdeal.one_notMem
  refine ⟨B (1 : A), le_top, hx, ?_⟩
  let i : B (1 : A) ⟶ (⊤ : (Spec A).Opens) := homOfLE le_top
  have h := (affineDifferentialAdditivePresheafMap_basicOpen k A (1 : A)
    (algebraMap A (affineDifferentialBasicOpenRing A 1) a)).trans
      (affineDifferentialBasicOpenDerivation_algebraMap k A 1 a)
  change (affineDifferentialAdditivePresheafMap k A).app (op (B (1 : A)))
      ((Spec A).presheaf.map i.op ((Scheme.ΓSpecIso A).inv a)) =
    tilde.toOpen (R := A) M (B (1 : A)) (KaehlerDifferential.D k A a) at h
  have hleft := (affineDifferentialAdditivePresheafMap_naturality k A i
    ((Scheme.ΓSpecIso A).inv a)).symm.trans h
  have hright := congrArg (fun t => t (KaehlerDifferential.D k A a))
    (tilde.toOpen_res (R := A) M ⊤ (B (1 : A)) i)
  exact hleft.trans hright.symm
end QEC.Coding.AlgebraicGeometry
