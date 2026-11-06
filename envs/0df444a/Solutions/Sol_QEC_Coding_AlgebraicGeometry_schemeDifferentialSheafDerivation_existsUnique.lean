-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeDifferentialSheafDerivation_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:19.017363+00:00
-- url     : https://prove2.me/submissions/cc925424-2fd4-4b34-a84b-bf121288ac14

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeDifferentials
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialSheaf_existsUnique
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialSheafDerivation_postcomp

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
theorem _root_.solution (M : X.Modules)
    (d : ((Scheme.Modules.toPresheafOfModules X).obj M).Derivation' constants) :
    ∃! f : Omega ⟶ M,
      (schemeDifferentialSheafDerivation X k c).postcomp
        ((Scheme.Modules.toPresheafOfModules X).map f) = d := by
  simpa only [schemeDifferentialSheafDerivation_postcomp] using
    schemeDifferentialSheaf_existsUnique X k c M d
end QEC.Coding.AlgebraicGeometry
