-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.card_filter_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:39:43.990589+00:00
-- url     : https://prove2.me/submissions/e5d994b5-293d-493b-92f4-149c919fb821

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SmulOneMemUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {N : ℕ} (Q : Fin N → Prop) [DecidablePred Q] (lo hi : ℕ) (hhi : hi ≤ N)
    (hQ : ∀ b : Fin N, Q b ↔ lo ≤ (b : ℕ) ∧ (b : ℕ) < hi) : (univ.filter Q).card = hi - lo := by
  have e : (univ.filter Q).map Fin.valEmbedding = Finset.Ico lo hi := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (hQ b).1 hb
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, by omega⟩, (hQ _).2 ⟨h1, h2⟩, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, e, Nat.card_Ico]
end ReciprocityTheory.ChartRestriction.DS.S7
