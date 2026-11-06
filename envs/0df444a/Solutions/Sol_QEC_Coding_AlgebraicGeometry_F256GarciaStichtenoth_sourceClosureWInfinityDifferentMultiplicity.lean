-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureWInfinityDifferentMultiplicity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:39:13.805417+00:00
-- url     : https://prove2.me/submissions/62a7c4ae-64c3-40a9-88f6-fbac901d50c6

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWGlobalPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFibreDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureW_integralModel_weakDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityRamificationIndex_eq_prime


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] closureDifferent_modelDedekind closureDifferent_modelFinite
  closureDifferent_modelFraction closureDifferent_modelTorsionFree
variable (m : ℕ)
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.fibreDifferent_baseAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.fibreDifferent_baseFraction
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.fibreDifferent_baseFaithful
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.fibreDifferent_baseDVR
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.fibreDifferent_ambientAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.fibreDifferent_baseTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.fibreDifferent_ambientTorsionFree
set_option maxHeartbeats 1000000
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (P : SourceGaloisWInfinityPrime m) :
    multiplicity P.1 (sourceClosurePlaceDifferentIdeal m (sourceGaloisWClosureInfinityPlace m)) =
      2 * (sourceGaloisWInfinityRamificationIndex m - 1) := by
  let A := (sourceGaloisWClosureInfinityPlace m).valuationRing
  let Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (SourceGaloisClosureField m)) :=
    sourceGaloisWInfinityUpperHeightOne m P
  letI : Algebra A (sourceClosureWBase m) := fibreDifferent_baseAlgebra m (sourceGaloisWClosureInfinityPlace m)
  letI : IsFractionRing A (sourceClosureWBase m) := fibreDifferent_baseFraction m (sourceGaloisWClosureInfinityPlace m)
  letI : IsScalarTower A (sourceClosureWBase m) (SourceGaloisClosureField m) :=
    fibreDifferent_baseTower m (sourceGaloisWClosureInfinityPlace m)
  have h := sourceClosureW_integralModel_weakDifferent m A Q
  have hp : (Q.under A).asIdeal = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Q.under A).isMaximal
  rw [hp] at h
  rw [sourceGaloisWInfinityRamificationIndex_eq_prime m P]
  exact h
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
