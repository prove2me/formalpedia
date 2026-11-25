-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_prod_mem_of_span_6204472a580c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:32:39.375925+00:00
-- url     : https://prove2.me/submissions/212decc7-d3f7-4408-9bd7-2100f354f106

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowGenMonomial
import Definitions.Def_Lemmata_GeneralBFactRightBisForm_Imports
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZLevB
import Theorems.Thm_Bl_general_b_fact_right_bis_form_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommGroup (M i)]
  [∀ i, Module R (M i)] {A : Type*} [CommRing A] [Algebra R A]
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (φ : ∀ i, M i →ₗ[R] A) (S : ∀ i, Set (M i)) (T : Submodule R A)
    (h : ∀ s : ∀ i, M i, (∀ i, s i ∈ S i) → ∏ i, φ i (s i) ∈ T) (m : ∀ i, M i)
    (hm : ∀ i, m i ∈ Submodule.span R (S i)) : ∏ i, φ i (m i) ∈ T := by
  first | exact Bl.general_b_fact_right_bis_form.goal1 .. | (apply Bl.general_b_fact_right_bis_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_bis_form.goal1 <;> assumption)
end Formalism.BasicNotions.Examples₂.NZ
