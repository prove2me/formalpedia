-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeDifferentialSheafDerivation_postcomp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:56:01.809206+00:00
-- url     : https://prove2.me/submissions/12f60b9a-a9a0-405b-b1fc-2b9f68e1383d

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeDifferentials

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (X : Scheme.{u}) (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
local notation "Omega" => schemeDifferentialSheaf X k c
local notation "constants" => schemeConstantPresheafMap X k c
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (M : X.Modules) (f : Omega ⟶ M) :
    (schemeDifferentialSheafDerivation X k c).postcomp
      ((Scheme.Modules.toPresheafOfModules X).map f) =
    schemeDifferentialSheafHomEquiv X k c M f := by
  ext U a
  rfl
end QEC.Coding.AlgebraicGeometry
