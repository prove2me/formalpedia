-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.prod_update_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:52:11.071442+00:00
-- url     : https://prove2.me/submissions/a38f19b5-a184-4ffd-a1a9-72cc167032fe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SupportSubsetMonoBox
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AbsProdSubProdSubLinLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {n : ℕ} (g : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    ∏ j, Function.update g i t j = t * (∏ j with j < i, g j) * ∏ j with i < j, g j := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ i), mul_assoc, ← Finset.prod_union
    (Finset.disjoint_filter.mpr fun j _ h1 h2 => lt_asymm h1 h2)]
  congr 2
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and, Finset.mem_union,
    Finset.mem_filter]
  constructor
  · intro h
    rcases lt_or_gt_of_ne h with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ne_of_lt h
    · exact ne_of_gt h
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
