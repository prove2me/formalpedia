-- Prove2me | solution 1 for PermanentFormulaLowerBound.coefficientTranscendenceDegree_ge_of_algebraicIndependent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/06c1782e-b0bb-434e-8a3d-07bfe415d861

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_coefficient_mem_coefficientField

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {Y Z F ι : Type*} [Field F] [Fintype ι]
    (p : MvPolynomial (Y ⊕ Z) F) (α : ι → Y →₀ ℕ)
    (hind : AlgebraicIndependent F
      (fun i => coefficientPolynomial p (α i))) :
    (Fintype.card ι : Cardinal) ≤ coefficientTranscendenceDegree p := by
  let φ : MvPolynomial Z F →ₐ[F] FractionRing (MvPolynomial Z F) :=
    IsScalarTower.toAlgHom F (MvPolynomial Z F)
      (FractionRing (MvPolynomial Z F))
  have hφ : Function.Injective φ :=
    IsFractionRing.injective (MvPolynomial Z F)
      (FractionRing (MvPolynomial Z F))
  have hfrac : AlgebraicIndependent F
      (fun i =>
        algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
          (coefficientPolynomial p (α i))) := by
    simpa [φ, Function.comp_def] using hind.map' hφ
  let g : ι → coefficientField p := fun i =>
    ⟨algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
      (coefficientPolynomial p (α i)),
      coefficient_mem_coefficientField p (α i)⟩
  have hg : AlgebraicIndependent F g := by
    apply
      (AlgHom.algebraicIndependent_iff
        (coefficientField p).val Subtype.val_injective).mp
    simpa [g, Function.comp_def] using hfrac
  change (Fintype.card ι : Cardinal) ≤
    Algebra.trdeg F (coefficientField p)
  simpa using hg.lift_cardinalMk_le_trdeg
end PermanentFormulaLowerBound
