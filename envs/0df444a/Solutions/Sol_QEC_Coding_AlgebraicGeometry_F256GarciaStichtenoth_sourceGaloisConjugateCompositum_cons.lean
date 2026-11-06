-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisConjugateCompositum_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:34:32.632194+00:00
-- url     : https://prove2.me/submissions/5cfef478-e7de-4b5e-8c18-a6f92b98c601

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
import Mathlib.Order.CompactlyGenerated.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosureFiniteCompositum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ)
    (s : Finset (SourceField m →ₐ[GaloisBaseField]
      SourceGaloisClosureAmbient))
    (f : SourceField m →ₐ[GaloisBaseField]
      SourceGaloisClosureAmbient)
    (hf : f ∉ s) :
    sourceGaloisConjugateCompositum m (s.cons f hf) =
      sourceGaloisConjugateCompositum m s ⊔ f.fieldRange := by
  unfold sourceGaloisConjugateCompositum
  apply le_antisymm
  · refine iSup_le fun g => iSup_le fun hg => ?_
    rcases Finset.mem_cons.mp hg with hgf | hgs
    · subst g
      exact le_sup_right
    · exact (le_iSup_of_le g
        (le_iSup (fun _ : g ∈ s => g.fieldRange) hgs)).trans le_sup_left
  · apply sup_le
    · refine iSup_le fun g => iSup_le fun hgs => ?_
      exact le_iSup_of_le g
        (le_iSup_of_le (Finset.mem_cons_of_mem hgs) le_rfl)
    · exact le_iSup_of_le f
        (le_iSup_of_le (Finset.mem_cons_self f s) le_rfl)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
