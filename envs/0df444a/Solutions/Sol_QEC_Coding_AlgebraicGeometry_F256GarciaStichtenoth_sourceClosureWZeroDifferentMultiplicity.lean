-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureWZeroDifferentMultiplicity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:40:50.506712+00:00
-- url     : https://prove2.me/submissions/d94bee8e-bd42-423a-bb52-377d4b6494f7

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWGlobalPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFibreDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureW_integralModel_weakDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroRamificationIndex_eq_prime


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
theorem _root_.solution (P : SourceGaloisWZeroPrime m) :
    multiplicity P.1 (sourceClosurePlaceDifferentIdeal m (sourceGaloisWClosureZeroPlace m)) =
      2 * (sourceGaloisWZeroRamificationIndex m - 1) := by
  let A := (sourceGaloisWClosureZeroPlace m).valuationRing
  let Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (SourceGaloisClosureField m)) :=
    sourceGaloisWZeroUpperHeightOne m P
  letI : Algebra A (sourceClosureWBase m) := fibreDifferent_baseAlgebra m (sourceGaloisWClosureZeroPlace m)
  letI : IsFractionRing A (sourceClosureWBase m) := fibreDifferent_baseFraction m (sourceGaloisWClosureZeroPlace m)
  letI : IsScalarTower A (sourceClosureWBase m) (SourceGaloisClosureField m) :=
    fibreDifferent_baseTower m (sourceGaloisWClosureZeroPlace m)
  have h := sourceClosureW_integralModel_weakDifferent m A Q
  have hp : (Q.under A).asIdeal = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Q.under A).isMaximal
  rw [hp] at h
  rw [sourceGaloisWZeroRamificationIndex_eq_prime m P]
  exact h
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
