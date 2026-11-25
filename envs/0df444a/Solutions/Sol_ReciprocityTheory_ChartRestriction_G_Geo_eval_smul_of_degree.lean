-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_of_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:32.092159+00:00
-- url     : https://prove2.me/submissions/c4648592-1fcd-4abb-ba99-6dd4de0359ee

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactMore_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaA_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodD
import Theorems.Thm_Bl_FirstBlockLemmaA_goal1
import Theorems.Thm_Bl_general_b_fact_more_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {k : Type*} [Field k]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {σ : Type*} [Fintype σ] (H : MvPolynomial σ k) (d : ℕ)
    (hH : ∀ m ∈ H.support, Finsupp.degree m = d) (c : k) (v : σ → k) :
    eval (c • v) H = c ^ d * eval v H := by
  first | exact Bl.FirstBlockLemmaA.goal1 .. | (apply Bl.FirstBlockLemmaA.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaA.goal1 <;> assumption)
end ReciprocityTheory.ChartRestriction.G.Geo
