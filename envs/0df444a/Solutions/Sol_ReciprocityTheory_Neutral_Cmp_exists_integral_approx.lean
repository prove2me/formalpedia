-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.exists_integral_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:25:22.100375+00:00
-- url     : https://prove2.me/submissions/e81efb2f-3f7b-40c7-9ffd-74fc306e879a

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ContinuousGK
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Inertia
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_padicAlgCl_norm_sub_le_max
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_denseRange


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
variable (F)
include F
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι)
    (x : PadicAlgCl p) (hx : ‖x‖ ≤ 1) : ∃ b : Ω, b ∈ A ∧ ‖x - ι b‖ < 1 := by
  obtain ⟨b, hb⟩ := (Metric.denseRange_iff.mp (denseRange F ι)) x 1 one_pos
  rw [dist_eq_norm] at hb
  refine ⟨b, (h b).2 ?_, hb⟩
  have e : ι b = x - (x - ι b) := by ring
  rw [e]
  exact (padicAlgCl_norm_sub_le_max _ _).trans (max_le hx hb.le)
end ReciprocityTheory.Neutral.Cmp
