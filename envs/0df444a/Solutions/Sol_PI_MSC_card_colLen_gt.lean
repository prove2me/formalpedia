-- Prove2me | solution 1 for PI.MSC.card_colLen_gt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:48.070062+00:00
-- url     : https://prove2.me/submissions/aa00fc88-8165-434d-ad68-073a75f581a9

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ShapeColumnDegreeColumnSizes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.MSC
namespace PI.MSC
theorem _root_.solution (ν : YoungDiagram) (t : ℕ) :
    (Finset.univ.filter fun c : Fin (ν.rowLen 0) => t < ν.colLen c).card = ν.rowLen t := by
  have hk : ν.rowLen t ≤ ν.rowLen 0 := ν.rowLen_anti 0 t (Nat.zero_le _)
  have hiff : ∀ c : Fin (ν.rowLen 0), t < ν.colLen c ↔ (c : ℕ) < ν.rowLen t := fun c => by
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
  simp_rw [hiff]
  rw [← Finset.card_map Fin.valEmbedding]
  have hm : (Finset.univ.filter fun c : Fin (ν.rowLen 0) => (c : ℕ) < ν.rowLen t).map Fin.valEmbedding =
      Finset.range (ν.rowLen t) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [hm, Finset.card_range]
end PI.MSC
