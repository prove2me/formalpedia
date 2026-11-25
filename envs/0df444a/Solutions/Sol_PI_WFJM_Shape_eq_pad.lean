-- Prove2me | solution 1 for PI.WFJM.Shape.eq_pad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:19:27.707212+00:00
-- url     : https://prove2.me/submissions/c8307406-54b9-4839-9381-b057ace29fa0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeFromFacts
import Theorems.Thm_PI_WFJM_Shape_length_lpos
import Theorems.Thm_PI_WFJM_Shape_length_lneg
import Theorems.Thm_PI_WFJM_Shape_pos_iff
import Theorems.Thm_PI_WFJM_Shape_neg_iff
import Theorems.Thm_PI_WFJM_Shape_nP_add_nN_le
import Theorems.Thm_PI_WFJM_Shape_natFloor_of_int
import Theorems.Thm_PI_WFJM_Shape_getD_pad
import Theorems.Thm_PI_WFJM_Shape_getD_lneg

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
    (hp : ∀ i i' : Fin n, i < i' → 0 < f i' → 0 < f i) (hn : ∀ i i' : Fin n, i < i' → f i < 0 → f i' < 0)
    (i : Fin n) :
    f i = (pad (lpos (αP f)) (n - (lpos (αP f)).length - (lneg (αN f)).length) (lneg (αN f))).getD i 0 := by
  have hAB := nP_add_nN_le f
  have hi := i.isLt
  simp only [getD_pad, length_lpos, length_lneg]
  split_ifs with h1 h2
  ·
    have hpos : 0 < f i := (pos_iff f hp i).2 h1
    simp only [lpos, List.getElem_ofFn, αP]
    have hci : Fin.castLE (nP_le_nW f) ⟨(i : ℕ), h1⟩ = i := Fin.ext rfl
    rw [hci]
    push_cast
    exact (natFloor_of_int (f i) ⌊f i⌋ (hint i) hpos.le).symm
  ·
    have hnp : ¬ 0 < f i := fun h => h1 ((pos_iff f hp i).1 h)
    have hnn : ¬ f i < 0 := fun h => by have := (neg_iff f hn i).1 h; omega
    linarith [not_lt.1 hnp, not_lt.1 hnn]
  ·
    have hneg : f i < 0 := (neg_iff f hn i).2 (by omega)
    rw [getD_lneg _ _ (by omega)]
    simp only [αN]
    have hci : Fin.rev (Fin.castLE (nN_le f) ⟨nN f - 1 - (i - nP f - (n - nP f - nN f)), by omega⟩) = i :=
      Fin.ext (by simp [Fin.val_rev]; omega)
    rw [hci]
    push_cast
    have := natFloor_of_int (-f i) (-⌊f i⌋) (by push_cast; rw [hint i]) (by linarith)
    rw [this]; ring
end PI.WFJM.Shape
