-- Prove2me | solution 1 for PI.HwUniqW.fix_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:55:44.395797+00:00
-- url     : https://prove2.me/submissions/ef912594-5618-4369-ae78-a8396b2801a9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
import Theorems.Thm_PI_HwUniqW_mulVec_bvec_apply
import Theorems.Thm_PI_HwUniqW_bvec_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.HwUniqW
open PI.UpqRep
variable {k r : ℕ}
namespace PI.HwUniqW
theorem _root_.solution {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : FixEW k r m)
    (j : Fin (2 * r + k + 1)) (hj : ¬ InB k r j) (i : Fin (2 * r + k + 1)) :
    m i j = if i = j then 1 else 0 := by
  have hcol : m *ᵥ bvec j = bvec j := by
    have hj' : ¬ (r ≤ j.val ∧ j.val < r + k) := hj
    have h0 := j.isLt
    obtain ⟨h1, h2⟩ := hm
    by_cases c1 : j.val < r
    · have e : j = eI k r ⟨j.val, c1⟩ := Fin.ext rfl
      rw [e]
      exact (h1 _).1
    · by_cases c2 : j.val = r + k
      · have e : j = wI k r (Fin.last k) := by
          apply Fin.ext
          show j.val = r + (Fin.last k).val
          rw [Fin.val_last]
          exact c2
        rw [e]
        exact h2
      · have e : j = esI k r ⟨2 * r + k - j.val, by omega⟩ := by
          apply Fin.ext
          show j.val = 2 * r + k - (2 * r + k - j.val)
          omega
        rw [e]
        exact (h1 _).2
  have e := congrFun hcol i
  rw [mulVec_bvec_apply, bvec_apply] at e
  exact e
end PI.HwUniqW
