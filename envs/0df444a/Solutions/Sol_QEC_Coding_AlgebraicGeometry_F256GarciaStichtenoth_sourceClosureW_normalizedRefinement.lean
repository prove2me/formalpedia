-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureW_normalizedRefinement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:59:31.84834+00:00
-- url     : https://prove2.me/submissions/d0e753eb-fda2-464d-b68d-62ab283ad75c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureConjugateChains
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedRefinement_finset_sup
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureConjugateW_normalized


set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] sourceConstantBaseTower
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ)
    (Q : GlobalPlace F256 (SourceGaloisClosureField m)) :
    PlaceNormalizedRefinement (sourceClosureWBase m) Q ⊥ ⊤ := by
  classical
  let E := SourceGaloisClosureField m
  let W := sourceClosureWBase m
  let I := SourceField m →ₐ[GaloisBaseField] E
  letI : Fintype I := Fintype.ofFinite I
  have hchains (f : I) := sourceClosureConjugateW_normalized m f Q
  let D (f : I) : IntermediateField W E :=
    IntermediateField.extendScalars (hchains f).choose
  have hD (f : I) : PlaceNormalizedRefinement W Q ⊥ (D f) := (hchains f).choose_spec
  let S : IntermediateField W E := Finset.univ.sup D
  have hS := PlaceNormalizedRefinement.finset_sup Q Finset.univ D (fun f _ => hD f)
  letI : Algebra GaloisBaseField (sourceClosureWBase m) :=
    inferInstanceAs (Algebra GaloisBaseField (SourceGaloisWClosureField m))
  letI : IsScalarTower GaloisBaseField (sourceClosureWBase m) (SourceGaloisClosureField m) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hbase (b : GaloisBaseField) : algebraMap GaloisBaseField E b ∈ S := by
    rw [IsScalarTower.algebraMap_apply GaloisBaseField W E]
    exact S.algebraMap_mem (algebraMap GaloisBaseField W b)
  let Sbase : IntermediateField GaloisBaseField E := S.toSubfield.toIntermediateField hbase
  have hclosure : IntermediateField.normalClosure GaloisBaseField (SourceField m) E = ⊤ :=
    (Algebra.IsAlgebraic.isNormalClosure_iff.mp
      (inferInstance : IsNormalClosure GaloisBaseField (SourceField m) E)).2
  have hle : IntermediateField.normalClosure GaloisBaseField (SourceField m) E ≤ Sbase := by
    apply normalClosure_le_iff.mpr
    intro f z hz
    exact (show D f ≤ S from Finset.le_sup (Finset.mem_univ f)) hz
  rw [hclosure] at hle
  have htop : S = ⊤ := by
    apply top_unique
    intro z _
    exact hle (show z ∈ (⊤ : IntermediateField GaloisBaseField E) from trivial)
  change PlaceNormalizedRefinement W Q ⊥ S at hS
  rwa [htop] at hS
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
