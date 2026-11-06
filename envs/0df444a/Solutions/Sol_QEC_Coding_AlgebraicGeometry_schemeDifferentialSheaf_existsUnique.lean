-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeDifferentialSheaf_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:58:46.588188+00:00
-- url     : https://prove2.me/submissions/f3683c3a-ba38-4ff7-93f0-2e65958d5a41

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
variable (X : Scheme.{u}) (k : CommRingCat.{u})
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (c : k ⟶ Γ(X, ⊤))
    (M : X.Modules)
    (d : ((Scheme.Modules.toPresheafOfModules X).obj M).Derivation'
      (schemeConstantPresheafMap X k c)) :
    ∃! f : schemeDifferentialSheaf X k c ⟶ M,
      schemeDifferentialSheafHomEquiv X k c M f = d := by
  refine ⟨(schemeDifferentialSheafHomEquiv X k c M).symm d, ?_, ?_⟩
  · exact (schemeDifferentialSheafHomEquiv X k c M).apply_symm_apply d
  · intro f hf
    apply (schemeDifferentialSheafHomEquiv X k c M).injective
    rw [hf, Equiv.apply_symm_apply]
end QEC.Coding.AlgebraicGeometry
