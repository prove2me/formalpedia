-- Prove2me | solution 1 for P2M_PI_WFJM_Shape_pos_of__N_cf6537b449c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:40.569248+00:00
-- url     : https://prove2.me/submissions/bc3e16de-5041-4f10-b111-4700e174eb61

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeFromFacts
import Theorems.Thm_PI_WFJM_Shape_neg_iff
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
    (hn : ∀ i i' : Fin n, i < i' → f i < 0 → f i' < 0) (i : Fin (nN f)) : 0 < αN f i := by
  have hneg : f (Fin.rev (Fin.castLE (nN_le f) i)) < 0 :=
    (neg_iff f hn _).2 (by simp [Fin.val_rev]; omega)
  have := natFloor_of_int (-f (Fin.rev (Fin.castLE (nN_le f) i))) (-⌊f (Fin.rev (Fin.castLE (nN_le f) i))⌋)
    (by push_cast; rw [hint]) (by linarith)
  unfold αN
  have h2 : (0 : ℚ) < ((⌊-f (Fin.rev (Fin.castLE (nN_le f) i))⌋₊ : ℕ) : ℚ) := by rw [this]; linarith
  exact_mod_cast h2
end PI.WFJM.Shape
