-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.exists_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:46:06.455625+00:00
-- url     : https://prove2.me/submissions/4e64bd61-1c64-4d0a-a68b-0c89b3e086da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorHensel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_sqrt_mem
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (hl : l ≠ 2) (c : ℂ_[l]) (hc : c ∈ MaximalUnramifiedExtension l) (h1 : ‖c‖ = 1) :
    ∃ b ∈ MaximalUnramifiedExtension l, b ^ 2 = c ∧ ‖b‖ = 1 := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq c two_pos
  have hb1 : ‖b‖ = 1 := by
    have : ‖b‖ ^ 2 = 1 := by rw [← norm_pow, hb, h1]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg b) two_ne_zero).1 this
  exact ⟨b, sqrt_mem l hl c b hc hb1 hb, hb, hb1⟩
end ReciprocityTheory.ChartRestriction.L1
