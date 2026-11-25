-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.weylK_shift_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:57.207539+00:00
-- url     : https://prove2.me/submissions/59c304c3-726c-436d-983b-883cb89a0aaa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylRatio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylRatio_prodW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (s : Fin n) (c : ℝ) :
    weylK ε (Λ + Pi.single s c) *
        ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s), ((Λ + rhoC ε) s - (Λ + rhoC ε) b) =
      weylK ε Λ *
        ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s), ((Λ + rhoC ε) s - (Λ + rhoC ε) b + c) := by
  rw [← weylRatio_prodW ε s (fun b => (Λ + rhoC ε) s - (Λ + rhoC ε) b),
    ← weylRatio_prodW ε s (fun b => (Λ + rhoC ε) s - (Λ + rhoC ε) b + c)]
  simp only [weylK]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  have hab : a ≠ b := ne_of_lt hb.1
  by_cases hbs : b = s
  · subst hbs
    simp only [Pi.add_apply, Pi.single_apply, hab, ↓reduceIte]
    ring
  · by_cases has : a = s
    · subst has
      simp only [Pi.add_apply, Pi.single_apply, hbs, ↓reduceIte]
      ring
    · simp only [Pi.add_apply, Pi.single_apply, hbs, has, ↓reduceIte]
      ring
end ReciprocityTheory.ChartRestriction.DS.HW
