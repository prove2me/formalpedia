-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_prod_63b54f0252db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:57:28.995488+00:00
-- url     : https://prove2.me/submissions/aee8ffb4-2ff1-45c9-867d-9374b5bf56f0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChoice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_mul_dc8f078d9407
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_one_f1d8f695b8c6

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
theorem _root_.solution {β : Type*} (s : Finset β) (f : β → MRingOver R ι) (a : β → K → ℕ)
    (h : ∀ b ∈ s, IsMultiHomog (f b) (a b)) : IsMultiHomog (∏ b ∈ s, f b) (∑ b ∈ s, a b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using homog_one (R := R) (ι := ι)
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    exact homog_mul (h b (Finset.mem_insert_self b s))
      (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))
end GroundTheory.Heights₂.Heights.Inter.Choice
