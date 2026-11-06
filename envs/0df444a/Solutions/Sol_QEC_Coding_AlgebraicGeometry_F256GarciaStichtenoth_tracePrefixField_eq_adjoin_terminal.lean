-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.tracePrefixField_eq_adjoin_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:16:24.141478+00:00
-- url     : https://prove2.me/submissions/1baf0e77-7ff4-4dcc-86a0-bbe5b0568882

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement

set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (K : IntermediateField F E) (t : ℕ → E) (ht : t 0 ∈ K) (n : ℕ)
    (heq : ∀ j < n, t (j + 1) ^ 2 + t (j + 1) = t j) :
    tracePrefixField K t n = (K⟮t n⟯).restrictScalars F := by
  induction n with
  | zero =>
      rw [tracePrefixField, IntermediateField.restrictScalars_adjoin_eq_sup]
      exact (sup_eq_left.mpr (IntermediateField.adjoin_simple_le_iff.mpr ht)).symm
  | succ n ih =>
      rw [tracePrefixField, IntermediateField.restrictScalars_adjoin_eq_sup,
        ih (fun j hj => heq j (by omega)),
        IntermediateField.restrictScalars_adjoin_eq_sup,
        IntermediateField.restrictScalars_adjoin_eq_sup, sup_assoc]
      have hle : F⟮t n⟯ ≤ F⟮t (n + 1)⟯ := by
        rw [IntermediateField.adjoin_simple_le_iff, ← heq n (by omega)]
        have ht' := IntermediateField.mem_adjoin_simple_self F (t (n + 1))
        exact (F⟮t (n + 1)⟯).add_mem
          ((F⟮t (n + 1)⟯).toSubalgebra.pow_mem ht' 2) ht'
      rw [sup_eq_right.mpr hle]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
