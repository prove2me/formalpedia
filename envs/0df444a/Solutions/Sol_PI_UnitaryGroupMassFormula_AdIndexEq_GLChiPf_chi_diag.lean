-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf.chi_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:34:03.083813+00:00
-- url     : https://prove2.me/submissions/f63b79a1-979b-4ed1-a843-5e476b34dac6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_GLDelta
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_GLChiPf_chi_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
open Matrix
variable {k : Type} [Field k] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
theorem _root_.solution (χ : GL (Fin n) k →* ℚ) (hpos : ∀ g, 0 < χ g)
    (hz : ∀ d : kˣ, χ (Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom d) = 1)
    (D : Fin n → kˣ) : χ (dU D) = 1 := by
  have e : χ (dU D) = (χ.comp dU) (∏ i, Pi.mulSingle i (D i)) := by
    rw [Finset.univ_prod_mulSingle]; rfl
  rw [e, map_prod]
  exact Finset.prod_eq_one (fun i _ => chi_single χ hpos hz i (D i))
end PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
