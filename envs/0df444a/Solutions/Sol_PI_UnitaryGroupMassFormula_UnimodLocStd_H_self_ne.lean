-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.H_self_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:41.419307+00:00
-- url     : https://prove2.me/submissions/1791fc48-8e34-4df5-b748-3e6a872e72cc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepSingleSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_DescentStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_HNsmulNsmul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_area_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_detD_ne
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_stdH_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
  (m : Type) [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (L : PeriodPair) {v : m → ℂ} (hv : v ≠ 0) : stdH L m v v ≠ 0 := by
  rw [stdH_apply]
  have hA : area L ≠ 0 := by rw [area_eq]; exact abs_ne_zero.mpr (detD_ne L)
  refine mul_ne_zero ?_ (inv_ne_zero (by exact_mod_cast hA))
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by by_contra h; push_neg at h; exact hv (funext h)
  have hsum : (∑ j, v j * conj (v j)) = ((∑ j, Complex.normSq (v j) : ℝ) : ℂ) := by
    push_cast; exact Finset.sum_congr rfl fun j _ => Complex.mul_conj (v j)
  rw [hsum]
  have : 0 < ∑ j, Complex.normSq (v j) :=
    Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩
  exact_mod_cast this.ne'
end PI.UnitaryGroupMassFormula.UnimodLocStd
