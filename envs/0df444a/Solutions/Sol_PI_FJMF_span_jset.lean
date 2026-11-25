-- Prove2me | solution 1 for PI.FJMF.span_jset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:13:20.622049+00:00
-- url     : https://prove2.me/submissions/38ef7ac6-156d-46b5-82f7-ab553bd96415

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MinDeg
import Theorems.Thm_PI_FJM_jointHarmonicsIffLaplacians
import Theorems.Thm_PI_FockOneDegW_Core_key
import Theorems.Thm_PI_WFJM_jointHarmonicsIffLaplacians


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMF
variable {p q r s : ℕ}
namespace PI.FJMF
theorem _root_.solution (P : Pol p q r s) (hP : P ∈ Submodule.span ℂ (Jset p q r s)) : P ∈ Jset p q r s := by
  have key := PI.FJM.jointHarmonicsIffLaplacians p q r s
  induction hP using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    exact (key 0).2 ⟨fun i j => map_zero _, fun i j => map_zero _, fun k l => map_zero _,
      fun k l => map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a1, a2, a3, a4⟩ := (key x).1 hx
    obtain ⟨b1, b2, b3, b4⟩ := (key y).1 hy
    exact (key (x + y)).2 ⟨fun i j => by rw [map_add, a1, b1, add_zero],
      fun i j => by rw [map_add, a2, b2, add_zero], fun k l => by rw [map_add, a3, b3, add_zero],
      fun k l => by rw [map_add, a4, b4, add_zero]⟩
  | smul c x _ hx =>
    obtain ⟨a1, a2, a3, a4⟩ := (key x).1 hx
    exact (key (c • x)).2 ⟨fun i j => by rw [map_smul, a1, smul_zero],
      fun i j => by rw [map_smul, a2, smul_zero], fun k l => by rw [map_smul, a3, smul_zero],
      fun k l => by rw [map_smul, a4, smul_zero]⟩
end PI.FJMF
