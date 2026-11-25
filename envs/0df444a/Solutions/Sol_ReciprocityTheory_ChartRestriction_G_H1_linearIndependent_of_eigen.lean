-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.linearIndependent_of_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:07:57.247285+00:00
-- url     : https://prove2.me/submissions/d19f1d42-9036-4d14-b951-cd1d5798a3cc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ReducedBasisStatement
import Definitions.Def_Lemmata_GeneralBFactExtra_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_NakayamaChar
import Theorems.Thm_P2M_Bl_general_b_fact____goal1_395295db5b2f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open Module TensorProduct
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution {K V ι Γ : Type} [Field K] [AddCommGroup V] [Module K V]
    (T : Γ → V →ₗ[K] V) (c : ι → Γ → K) (w : ι → V) (hw : ∀ i, w i ≠ 0)
    (he : ∀ i γ, T γ (w i) = c i γ • w i) (hd : ∀ i j, i ≠ j → ∃ γ, c i γ ≠ c j γ) :
    LinearIndependent K w := by
  first | exact Bl.general_b_fact'''.goal1 .. | (apply Bl.general_b_fact'''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact'''.goal1 <;> assumption)
end ReciprocityTheory.ChartRestriction.G.H1
