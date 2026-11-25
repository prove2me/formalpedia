-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_sum_690e475d4993
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:53:02.177382+00:00
-- url     : https://prove2.me/submissions/09bbd2a7-e202-4851-9d8c-ac0f7b021352

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChoice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_zero_e6cefdcfb9f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_add_a96a59fb7624

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.Choice
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.Inter.Choice
theorem _root_.solution {β : Type*} (s : Finset β) (f : β → MRingOver R ι) {a : K → ℕ}
    (h : ∀ b ∈ s, IsMultiHomog (f b) a) : IsMultiHomog (∑ b ∈ s, f b) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using homog_zero (R := R) (ι := ι) a
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    exact homog_add (h b (Finset.mem_insert_self b s))
      (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))
end GroundTheory.Heights₂.Heights.Inter.Choice
