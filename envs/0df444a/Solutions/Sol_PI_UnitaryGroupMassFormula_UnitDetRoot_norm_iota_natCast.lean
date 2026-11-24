-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.norm_iota_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:30:26.993326+00:00
-- url     : https://prove2.me/submissions/97677fdf-3d01-41f5-a545-7e5f977f7235

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Lemmata_GeneralBFactLeftTer_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NormLeOneOfRoot

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (k : ℕ) (hk : ¬ l ∣ k) :
    ‖ι (k : ℂ)‖ = 1 := by
  rw [map_natCast]
  have e : ((k : ℚ_[l]) : ℂ_[l]) = (k : ℂ_[l]) := by simp
  rw [← e, PadicComplex.norm_extends', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hk
end PI.UnitaryGroupMassFormula.UnitDetRoot
