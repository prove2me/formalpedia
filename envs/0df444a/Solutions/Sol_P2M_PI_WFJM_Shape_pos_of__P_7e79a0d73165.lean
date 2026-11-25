-- Prove2me | solution 1 for P2M_PI_WFJM_Shape_pos_of__P_7e79a0d73165
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:44.195713+00:00
-- url     : https://prove2.me/submissions/94bad241-13a7-4aaf-84ce-27605fc25c55

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeFromFacts
import Theorems.Thm_PI_WFJM_Shape_pos_iff
import Theorems.Thm_PI_WFJM_Shape_natFloor_of_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM PI.WFJM.Shape
open PI.FJM
variable {n : ℕ}
namespace PI.WFJM.Shape
theorem _root_.solution (f : Fin n → ℚ) (hint : ∀ i, ((⌊f i⌋ : ℤ) : ℚ) = f i)
    (hp : ∀ i i' : Fin n, i < i' → 0 < f i' → 0 < f i) (i : Fin (nP f)) : 0 < αP f i := by
  have hpos : 0 < f (Fin.castLE (nP_le_nW f) i) := (pos_iff f hp _).2 (by simp)
  have := natFloor_of_int _ _ (hint (Fin.castLE (nP_le_nW f) i)) hpos.le
  unfold αP
  have h2 : (0 : ℚ) < ((⌊f (Fin.castLE (nP_le_nW f) i)⌋₊ : ℕ) : ℚ) := by rw [this]; exact hpos
  exact_mod_cast h2
end PI.WFJM.Shape
