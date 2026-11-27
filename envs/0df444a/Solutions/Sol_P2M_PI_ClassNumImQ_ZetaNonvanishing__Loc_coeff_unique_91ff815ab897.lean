-- Prove2me | solution 1 for P2M_PI_ClassNumImQ_ZetaNonvanishing__Loc_coeff_unique_91ff815ab897
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:14:40.202021+00:00
-- url     : https://prove2.me/submissions/d5531645-99d6-4d28-bb2e-a6bf7686d0f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_Development
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ClassNumImQInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticInvariants_QuadPolyIrreducible
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_LocOdd
import Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__Loc_om_coe_5fa917f41074
import Theorems.Thm_PI_UnitaryGroupMassFormula_ClassNumImQInv_b_ne_rat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.ClassNumImQ PI.ClassNumImQ.ZetaNonvanishing₂ PI.ClassNumImQ.ZetaNonvanishing₂.Loc
variable {d : ℕ} {K : Type} [Field K] [NumberField K] {b : K}
namespace PI.ClassNumImQ.ZetaNonvanishing₂.Loc
theorem _root_.solution (hq : QuadData d K b) {m n m' n' : ℤ}
    (h : (m : 𝓞 K) + n * om hq = m' + n' * om hq) : m = m' ∧ n = n' := by
  have hK : (m : K) + n * ((1 + b) / 2) = m' + n' * ((1 + b) / 2) := by
    have h' := congrArg (fun x : 𝓞 K => (x : K)) h
    push_cast [om_coe] at h'
    exact h'
  by_cases hn : n = n'
  · subst hn
    refine ⟨?_, rfl⟩
    exact_mod_cast add_right_cancel hK
  · exfalso
    have hne : ((n : K) - n') ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn)
    apply PI.UnitaryGroupMassFormula.ClassNumImQInv.b_ne_rat hq ((2 * (m' - m) + n' - n) / (n - n'))
    push_cast
    rw [div_eq_iff hne]
    linear_combination (-2 : K) * hK
end PI.ClassNumImQ.ZetaNonvanishing₂.Loc
