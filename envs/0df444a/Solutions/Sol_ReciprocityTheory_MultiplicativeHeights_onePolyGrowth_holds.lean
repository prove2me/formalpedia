-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.onePolyGrowth_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:12:54.851068+00:00
-- url     : https://prove2.me/submissions/87a225f9-fd43-4e24-85f7-2eb73bb478df

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Lemmata_IterateZero_IterZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_OnePolyGrowth
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_entire_poly_of_growth
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_exists_entire_of_finite_growth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Filter Topology Function Metric Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution : OnePolyGrowthStatement := by
  intro f B A k hB hf hb
  obtain ⟨g, hg, hgf⟩ := exists_entire_of_finite_growth f B A k hB hf hb
  have hclosed : IsClosed {t : ℂ | ‖g t‖ ≤ A * (1 + ‖t‖) ^ k} :=
    isClosed_le (continuous_norm.comp hg.continuous)
      (continuous_const.mul ((continuous_const.add continuous_norm).pow k))
  have hsub : Bᶜ ⊆ {t : ℂ | ‖g t‖ ≤ A * (1 + ‖t‖) ^ k} := fun t ht => by
    simpa [hgf t ht] using hb t ht
  have hall : ∀ t, ‖g t‖ ≤ A * (1 + ‖t‖) ^ k := by
    have hd : Dense Bᶜ := hB.countable.dense_compl ℂ
    intro t
    have : t ∈ closure Bᶜ := by rw [hd.closure_eq]; trivial
    exact closure_minimal hsub hclosed this
  obtain ⟨P, hPd, hP⟩ := entire_poly_of_growth k g A hg hall
  exact ⟨P, hPd, fun t ht => by rw [← hgf t ht, hP t]⟩
end ReciprocityTheory.MultiplicativeHeights
